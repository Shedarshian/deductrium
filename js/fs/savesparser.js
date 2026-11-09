import { ASTParser } from "./astparser.js";
import { initFormalSystem } from "./initial.js";
import { RuleParser } from "./metarule.js";
import { ASTMgr } from "./astmgr.js";
import { containsModelOperation, templateNames } from "./model.js";
const astparser = new ASTParser;
export class SavesParser {
    creative = false;
    constructor(creative) {
        this.creative = creative;
        this.bug260616fixer.fixbug260616 = true;
    }
    serializeDeductionStep(s) {
        const step = [
            s.deductionIdx, s.conditionIdxs,
            s.replaceValues.map(v => astparser.stringifySaved(v))
        ];
        if (s.model)
            step.push({ path: s.model.path.slice(), target: astparser.stringifySaved(s.model.target) });
        return step;
    }
    serializeProposition(p) {
        const value = astparser.stringifySaved(p.value);
        const step = p.from ? this.serializeDeductionStep(p.from) : null;
        return [value, step];
    }
    deserializeDeductionStep(v) {
        return { conditionIdxs: v[1], deductionIdx: v[0], replaceValues: v[2].map(v => astparser.parseSaved(v)),
            model: v[3] ? { path: v[3].path.slice(), target: astparser.parseSaved(v[3].target) } : undefined };
    }
    deserializeProposition(v) {
        return {
            value: astparser.parseSaved(v[0]),
            from: v[1] ? this.deserializeDeductionStep(v[1]) : null
        };
    }
    serializeDeduction(deduction) {
        const value = astparser.stringifySaved(deduction.value);
        const steps = deduction.steps?.map(s => this.serializeDeductionStep(s));
        // if fs has tempvars record, then serialize it
        return deduction.tempvars?.size ? [value, deduction.from, steps, Array.from(deduction.tempvars)] : [value, deduction.from, steps];
    }
    // 26-3-30: bug fix: rule "<.a1_n" not exist, use ":c{rec},.cs" instead
    fixbug260330_(num) {
        return num === 3 ? ":ca1,.cs" : (":c" + this.fixbug260330_(num - 1) + ",.cs");
    }
    fixbug260330(s) {
        const num = Number(s.match(/>\.a1\_([1-9][0-9]*)$/)[1]);
        return s.replace(/>\.a1\_([1-9][0-9]*)$/, this.fixbug260330_(num));
    }
    // rule :.=t is invalid but can be generated   ==convert it to==>   :.=t,.=t
    // use a wrong version parser to generate 
    bug260616fixer = new RuleParser;
    ruleparser = new RuleParser;
    fixbug260616(s) {
        if (s.split(":").length > s.split(",").length || s.split(":").length < s.split(",").length) {
            try {
                this.ruleparser.parse(s);
            }
            catch (e) {
                return this.bug260616fixer.stringify(this.bug260616fixer.parse(s));
            }
            return s;
        }
        return s;
    }
    deserializeDeduction(name, fs, sd) {
        // deserialized data is reliable, no need to regen tempvars
        // fix bugs for nested #nf funcs 26-7-5
        const val = astparser.parseSaved(sd[0]);
        try {
            fs.assert.expand(val, false);
        }
        catch (e) {
            if (containsModelOperation(val) || templateNames(val).size)
                throw e;
        }
        fs.addDeduction(name, val, sd[1], sd[2]?.map(e => this.deserializeDeductionStep([
            e[0].includes(">.a1_") ? this.fixbug260330(e[0]) : e[0].includes(":") ? this.fixbug260616(e[0]) : e[0], e[1], e[2], e[3]
        ])), sd[3] ? new Set(sd[3]) : new Set());
    }
    serialize(gui) {
        const fs = gui.formalSystem;
        const dlist = gui.deductions;
        const userD = {};
        for (const [n, d] of Object.entries(fs.deductions)) {
            // save a..x
            if (!d.from.endsWith("*") && !n.endsWith("x"))
                continue;
            if (n.startsWith("c") || n.startsWith("<") || n.startsWith(">") || n.startsWith("v") || n.startsWith("u") || n.startsWith("e") || n.startsWith(".")) {
                continue;
            }
            userD[n] = this.serializeDeduction(d);
        }
        const props = gui.getProps();
        return JSON.stringify([
            Array.from(fs.consts), Array.from(fs.fns), Array.from(fs.verbs), [[ /* todo metamacro */], ...gui.metarules], userD, dlist, props.map(s => this.serializeProposition(s))
        ]);
    }
    deserializeArr(fs, arr) {
        // 
        if (arr.length < 7)
            arr.splice(2, 0, [], []);
        const [arrC, arrFn, arrVb, arrM, dictD, arrD, arrP] = arr;
        for (const v of arrC) {
            fs.consts.add(v);
        }
        for (const v of arrFn) {
            fs.fns.add(v);
        }
        for (const v of arrVb) {
            fs.verbs.add(v);
        }
        for (const [k, v] of Object.entries(dictD)) {
            if (v.length)
                this.deserializeDeduction(k, fs, v);
        }
        const replay = arrP?.some(v => v[0].startsWith("@model-v1:") || /#(?:sat|abs|abst|absf)\(/.test(v[0]) || !!v[1]?.[3] || v[1]?.[2]?.some(s => s.startsWith("@model-v1:"))) ||
            Object.values(fs.deductions).some(d => fs.hasModelProof(d) || d.from.startsWith("模型解释:"));
        if (arrP)
            for (const v of arrP) {
                const p = this.deserializeProposition(v);
                if (p.from && replay) {
                    fs.assert.checkGrammer(p.value, "p");
                    const index = fs.deduct(p.from);
                    if (!new ASTMgr().equal(fs.propositions[index].value, p.value))
                        throw new Error("存档中的模型推理结论未通过重放核验");
                }
                else {
                    fs.assert.checkGrammer(p.value, "p");
                    fs.propositions.push(p);
                }
            }
        return { fs, arrD, arrM };
    }
    deserializeMetaMacro(gui, arr) {
        // todo
        gui.formalSystem.metaMacro = {};
    }
    deserialize(gui, str) {
        const skipRendering = gui.skipRendering;
        const previous = { fs: gui.formalSystem, deductions: gui.deductions, metarules: gui.metarules };
        gui.skipRendering = true;
        try {
            const fsArrD = initFormalSystem(this.creative);
            fsArrD.fs.fastmetarules = gui.formalSystem.fastmetarules;
            const fsdata = this.deserializeArr(fsArrD.fs, JSON.parse(str));
            const savedMetarules = gui.formalSystem.fastmetarules;
            gui.formalSystem = fsdata.fs;
            gui.formalSystem.fastmetarules = savedMetarules;
            gui.deductions = fsdata.arrD;
            // 25-11-25: bug fix player's progress
            if (gui.deductions.includes("apn3") && !gui.deductions.includes("apn4") && !gui.deductions.includes("apn5")) {
                gui.deductions.push("apn4", "apn5");
            }
            if (fsdata.arrM[0]) {
                gui.metarules = Array.from(new Set(fsdata.arrM.slice(1)));
                this.deserializeMetaMacro(gui, fsdata.arrM[0]);
            }
            gui.skipRendering = skipRendering;
            gui.updatePropositionList(true);
            gui.updateDeductionList();
            gui.updateMetaRuleList(true);
        }
        catch (e) {
            gui.formalSystem = previous.fs;
            gui.deductions = previous.deductions;
            gui.metarules = previous.metarules;
            throw e;
        }
        finally {
            gui.skipRendering = skipRendering;
        }
    }
}
//# sourceMappingURL=savesparser.js.map