import { ASTMgr } from "./astmgr.js";
import { AssertionSystem } from "./assertion.js";
import { Proof } from "./proof.js";
import { ASTParser } from "./astparser.js";
import { TR } from "../lang.js";
import { ConstrainSolver, RuleParser } from "./metarule.js";
import { defaultEvaluationLimits, EvaluationBudget, withBudget } from "./evaluation.js";
const astmgr = new ASTMgr;
const assert = new AssertionSystem;
const parser = new ASTParser;
const ruleparser = new RuleParser();
export class FormalSystem {
    evaluationLimits = { ...defaultEvaluationLimits };
    evaluation;
    generating = new Set();
    generationDepth = 0;
    proofCache = new Map();
    proofCacheSize = 0;
    generated = new Map();
    generatedWeights = new WeakMap();
    liftability = new WeakMap();
    isMacro(d) { return !!d && (d.steps !== undefined || d.proof !== undefined); }
    hasProofSteps(d) { return !!(d?.steps?.length || d?.proof?.length); }
    proofDependencies(d) {
        return d.proof?.dependencies ?? d.steps?.map(s => s.deductionIdx) ?? [];
    }
    canLift(root) {
        const cached = this.liftability.get(root);
        if (cached !== undefined)
            return cached;
        const visiting = new Set();
        const visited = new Set();
        const stack = [{ rule: root, exit: false }];
        while (stack.length) {
            this.evaluation?.check();
            const { rule, exit } = stack.pop();
            if (exit) {
                visiting.delete(rule);
                visited.add(rule);
                continue;
            }
            if (visited.has(rule) || this.liftability.get(rule) === true)
                continue;
            if (visiting.has(rule))
                throw new Error("循环证明依赖 / Cyclic proof dependency");
            if (!rule.liftable)
                return false;
            visiting.add(rule);
            stack.push({ rule, exit: true });
            // Inspect references, not transformed proof bodies. A conditional
            // primitive needs an existing admissibility certificate (the mp seed).
            for (const dependency of this.proofDependencies(rule)) {
                const atoms = [];
                this.getAtomDeductionTokens(dependency, atoms);
                for (const atom of atoms) {
                    if (atom === "#")
                        continue;
                    const child = this.generateDeduction(atom);
                    if (!child)
                        return false;
                    stack.push({ rule: child, exit: false });
                }
            }
        }
        for (const rule of visited)
            this.liftability.set(rule, true);
        return true;
    }
    getProofSteps(d) {
        return this.evaluate(() => this.getProofStepsChecked(d));
    }
    getProofStepsChecked(d) {
        if (d.steps !== undefined || !d.proof)
            return d.steps;
        const cached = this.proofCache.get(d);
        if (cached) {
            this.proofCache.delete(d);
            this.proofCache.set(d, cached);
            return cached.steps;
        }
        this.evaluation?.check();
        const steps = d.proof.load();
        let weight = steps.length;
        for (const step of steps) {
            weight += step.conditionIdxs.length;
            for (const value of step.replaceValues)
                weight += this.astWeight(value);
            if (weight > 100_000)
                break;
        }
        // Large bodies can be consumed without retaining a second resident copy.
        if (weight <= 100_000) {
            while (this.proofCacheSize + weight > 100_000 || this.proofCache.size >= 128) {
                const oldest = this.proofCache.keys().next().value;
                this.proofCacheSize -= this.proofCache.get(oldest).weight;
                this.proofCache.delete(oldest);
            }
            this.proofCache.set(d, { steps, weight });
            this.proofCacheSize += weight;
        }
        return steps;
    }
    addLazyDeduction(name, value, from, proof, tempvars = new Set(), liftable = false) {
        this.addDeduction(name, value, from, undefined, tempvars);
        this.deductions[name].proof = { ...proof, load: () => this.evaluate(() => proof.load()) };
        this.deductions[name].liftable = liftable;
        return name;
    }
    /** c/v are admissible for checked macros in this Hilbert calculus. Keep
     * the existing proof transformer as the explicit, one-level proof recipe.
     * Unknown conditional primitives still take its original checked path. */
    deferLift(op, input, from, build) {
        const name = op + input;
        if (this.deductions[name])
            return name;
        const d = this.generateDeduction(input);
        if (!d || (op === "v" && !this.isMacro(d)) || !this.canLift(d))
            return build();
        const variable = this._findNewReplName(input);
        const wrap = (ast) => ({ type: "sym", name: op === "c" ? ">" : "V", nodes: [astmgr.clone(variable), astmgr.clone(ast)] });
        // addHypothese/expand retain the assertion normalization used by the
        // proof transformer, without visiting any of the input's subproofs.
        const oldP = this.propositions;
        let conditions;
        const conclusion = wrap(d.conclusion);
        try {
            this.propositions = [];
            d.conditions.forEach(c => this.addHypothese(wrap(c)));
            conditions = this.propositions.map(p => p.value);
            assert.expand(conclusion, false);
        }
        finally {
            this.propositions = oldP;
        }
        const value = { type: "meta", name: "⊢", nodes: [
                { type: "fn", name: "#array", nodes: conditions },
                { type: "fn", name: "#array", nodes: [conclusion] }
            ] };
        let rule;
        this.addLazyDeduction(name, value, from, {
            length: 1, dependencies: [input],
            load: () => {
                // Do not mutate the entry held by previews or other recipes.
                // Nested lifts may be registered, but this temporary eager body
                // is returned to the bounded proof cache rather than published.
                const previous = this.deductions[name];
                const oldP = this.propositions;
                const fmr = this.fastmetarules;
                const generated = this.generated.get(name);
                delete this.deductions[name];
                try {
                    const built = this.deductions[build()];
                    if (!astmgr.equal(rule.value, built.value))
                        throw new Error("延迟证明签名不一致 / Deferred proof signature mismatch: " + name);
                    return this.getProofSteps(built);
                }
                finally {
                    this.deductions[name] = previous;
                    if (generated)
                        this.generated.set(name, generated);
                    else
                        this.generated.delete(name);
                    this.propositions = oldP;
                    this.fastmetarules = fmr;
                }
            }
        }, new Set(d.tempvars), true);
        rule = this.deductions[name];
        this.liftability.set(rule, true);
        if (this.generationDepth)
            this.generated.set(name, rule);
        return name;
    }
    invalidateGenerated() {
        for (const [name, d] of this.generated) {
            if (this.deductions[name] === d)
                delete this.deductions[name];
        }
        this.generated.clear();
        this.proofCache.clear();
        this.proofCacheSize = 0;
        this.liftability = new WeakMap();
    }
    astWeight(ast) {
        const stack = [ast];
        let weight = 0;
        while (stack.length && weight <= 100_000) {
            const value = stack.pop();
            weight++;
            if (value.nodes)
                for (const node of value.nodes)
                    stack.push(node);
        }
        return weight;
    }
    generateRule(action) {
        return this.evaluate(() => {
            this.generationDepth++;
            try {
                return action();
            }
            finally {
                this.generationDepth--;
            }
        });
    }
    generateLiteral(action) {
        return this.generateRule(() => {
            const name = action();
            // Literal templates are built by the kernel, and their c/v
            // admissibility does not require enumerating numeric subproofs.
            if (name)
                this.liftability.set(this.deductions[name], true);
            return name;
        });
    }
    /** Atomic synchronous operation, including all nested rule generation. */
    evaluate(action) {
        if (this.evaluation) {
            this.evaluation.enter();
            try {
                return action();
            }
            finally {
                this.evaluation.leave();
            }
        }
        const propositions = this.propositions;
        const saved = propositions.slice();
        const deductions = { ...this.deductions };
        const generated = new Map(this.generated);
        const fastmetarules = this.fastmetarules;
        this.evaluation = new EvaluationBudget(this.evaluationLimits);
        try {
            return withBudget(this.evaluation, action);
        }
        catch (e) {
            propositions.length = 0;
            for (const proposition of saved)
                propositions.push(proposition);
            this.propositions = propositions;
            this.deductions = deductions;
            this.generated = generated;
            throw e;
        }
        finally {
            this.evaluation = undefined;
            this.fastmetarules = fastmetarules;
            // Derived entries are reproducible by name. Never evict user/initial rules.
            for (const [name, d] of this.generated) {
                if (this.deductions[name] !== d)
                    this.generated.delete(name);
            }
            let weight = 0;
            for (const d of this.generated.values()) {
                if (!this.generatedWeights.has(d)) {
                    let size = this.astWeight(d.value);
                    for (const step of d.steps ?? []) {
                        size += 1 + step.conditionIdxs.length;
                        for (const value of step.replaceValues)
                            size += this.astWeight(value);
                        if (size > 100_000)
                            break;
                    }
                    this.generatedWeights.set(d, size);
                }
                weight += this.generatedWeights.get(d);
            }
            while (this.generated.size > 512 || weight > 100_000) {
                const name = this.generated.keys().next().value;
                const d = this.generated.get(name);
                weight -= this.generatedWeights.get(d);
                if (this.deductions[name] === d)
                    delete this.deductions[name];
                this.generated.delete(name);
            }
        }
    }
    deductions = {};
    metaRules = {};
    metaMacro = {};
    fastmetarules = "";
    disabledMetaRules = [];
    deductionReplNameRule = /^\$/g;
    localNameRule = /^\#/g;
    localReplacedNameRule = /^\#\#/g;
    // replacedLocalNameRule: RegExp = /^&/g;
    // ignoreNfNameRule: RegExp = /^(&|#)/g;
    // fnParamNames = (n: number) => "#" + n;
    consts = new Set();
    fns = new Set();
    verbs = new Set();
    propositions = [];
    assert = assert;
    constructor() {
        this.assert.fns = this.fns;
        this.assert.verbs = this.verbs;
        this.assert.consts = this.consts;
    }
    ast2deduction(ast) {
        assert.checkGrammer(ast, "d");
        const [conditions, conclusions] = ast.nodes;
        const varLists = {};
        const allReplvars = new Set;
        const matchingReplvars = new Set;
        conditions.nodes.map(c => {
            assert.getReplVarsType(c, varLists, false);
            astmgr.getVarNames(c, allReplvars, /^\$/);
            const netC = astmgr.clone(c);
            assert.unwrapAssertions(netC);
            astmgr.getVarNames(netC, matchingReplvars, /^\$/);
            return netC;
        });
        assert.getReplVarsType(conclusions.nodes[0], varLists, false);
        astmgr.getVarNames(conclusions, allReplvars, /^\$/);
        return {
            value: ast,
            conclusion: conclusions.nodes[0],
            conditions: conditions.nodes,
            replaceNames: Array.from(allReplvars).filter(e => !matchingReplvars.has(e)),
            replaceTypes: varLists,
            from: "",
            tempvars: null
        };
    }
    ast2metaRule(ast) {
        let grammarCheck = ast.type === "meta" && ast.name === "⊢M" && ast.nodes?.length === 2;
        if (!grammarCheck)
            throw TR("未找到元推理符号");
        const [conditions, conclusions] = ast.nodes;
        if (!conclusions.nodes?.length)
            throw TR("元推理符号后面没有结论");
        return {
            value: ast,
            conclusions: conclusions.nodes,
            conditions: conditions.nodes,
            replaceNames: [], conditionDeductionIdxs: [],
            from: ""
        };
    }
    getdependency(name, deductionIdx) {
        if (!deductionIdx)
            return false;
        const res = [];
        this.getAtomDeductionTokens(deductionIdx, res);
        return name === deductionIdx || res.includes(name);
    }
    removeDeduction(name) {
        if (!this.generateDeduction(name))
            throw TR("规则名称 ") + name + TR(" 不存在");
        if (this.getDeductionTokens(name).length > 1)
            return false; // this is composed, ignore it
        const composedDs = [];
        for (const [n, d] of Object.entries(this.deductions)) {
            if (!this.isMacro(d))
                continue;
            if (name === n)
                continue;
            if (this.getDeductionTokens(n).length > 1) {
                if (this.getdependency(name, n))
                    composedDs.push(n);
                continue;
            }
            for (const dependency of this.proofDependencies(d)) {
                if (this.getdependency(name, dependency)) {
                    throw TR("无法删除规则 ") + name + TR("，请先删除对其有依赖的规则 ") + n;
                }
            }
        }
        for (const [n, p] of this.propositions.entries()) {
            if (this.getdependency(name, p.from?.deductionIdx)) {
                throw TR("无法删除规则 ") + name + TR("，请先删除对其有依赖的定理 p") + n;
            }
        }
        if (name.startsWith("dc")) {
            this.consts.delete(name.slice(2));
        }
        if (name.startsWith("df")) {
            this.fns.delete(name.slice(2));
        }
        if (name.startsWith("dv")) {
            this.verbs.delete(name.slice(2));
        }
        for (const d of composedDs) {
            delete this.deductions[d];
        }
        delete this.deductions[name];
        this.invalidateGenerated();
        return true;
    }
    renameDeduction(oldname, newname) {
        if (this.getDeductionTokens(oldname).length > 1 || this.getDeductionTokens(newname).length > 1)
            throw TR("无法重命名快速元规则");
        if (oldname.match(/^[mad\.]/)) {
            throw TR("无法重命名系统规则");
        }
        if (!this.deductions[oldname])
            throw TR("规则名称 ") + oldname + TR(" 不存在");
        if (this.deductions[newname])
            throw TR("规则名称 ") + newname + TR(" 已存在");
        const composedDs = [];
        for (const [n, d] of Object.entries(this.deductions)) {
            if (!this.isMacro(d))
                continue;
            if (oldname === n)
                continue;
            if (this.getDeductionTokens(n).length > 1) {
                if (this.getdependency(oldname, n)) {
                    composedDs.push(n);
                }
                continue;
            }
            if (!this.proofDependencies(d).some(dependency => this.getdependency(oldname, dependency)))
                continue;
            // Publish a new entry: preview snapshots may still reference the old one.
            const steps = this.getProofSteps(d).map(s => ({ ...s, conditionIdxs: [...s.conditionIdxs] }));
            this.deductions[n] = { ...d, steps, proof: undefined };
            for (const s of steps) {
                if (this.getdependency(oldname, s.deductionIdx)) {
                    const tr = this.getDeductionTokens(s.deductionIdx);
                    ruleparser.replaceNameByName(tr, oldname, newname);
                    s.deductionIdx = ruleparser.stringify(tr);
                }
            }
        }
        for (const [n, p] of this.propositions.entries()) {
            const s = p.from;
            if (!s)
                continue;
            if (this.getdependency(oldname, s.deductionIdx)) {
                const tr = this.getDeductionTokens(s.deductionIdx);
                ruleparser.replaceNameByName(tr, oldname, newname);
                s.deductionIdx = ruleparser.stringify(tr);
            }
        }
        for (const d of composedDs) {
            delete this.deductions[d];
        }
        this.deductions[newname] = this.deductions[oldname];
        delete this.deductions[oldname];
        this.invalidateGenerated();
    }
    addDeduction(name, d, from, macro, tempvars) {
        const deduction = this.ast2deduction(d);
        deduction.from = from;
        deduction.steps = macro;
        deduction.tempvars = tempvars ?? this.findLocalNamesInDeductionStep(macro);
        deduction.liftable = !macro ? deduction.conditions.length === 0 :
            (this.generationDepth > 0 || macro.every(s => this.deductions[s.deductionIdx]?.liftable));
        if (this.deductions[name])
            throw TR("规则名称 ") + name + TR(" 已存在");
        this.deductions[name] = deduction;
        if (this.generationDepth)
            this.generated.set(name, deduction);
        return name;
    }
    addMetaRule(name, m, conditionDeductionIdxs, replaceNames, from) {
        const metaRule = this.ast2metaRule(m);
        metaRule.from = from;
        metaRule.conditionDeductionIdxs = conditionDeductionIdxs;
        metaRule.replaceNames = replaceNames;
        this.metaRules[name] = metaRule;
    }
    addMetaMacro(name, inputs, output, from) {
        if (this.metaRules[name])
            throw TR("元规则 ") + name + TR(" 已存在");
        for (const i of inputs) {
            if (i.startsWith("$$"))
                throw TR("元规则输入中不能包含以$$开头的变量");
        }
        const replaceInTree = (tree) => {
            if (tree.length === 1) {
                if (inputs.includes(tree[0])) {
                    tree[0] = "$$" + tree[0];
                }
            }
            else {
                for (let i = 1; i < tree.length; i++) {
                    replaceInTree(tree[i]);
                }
            }
        };
        replaceInTree(output);
        inputs = inputs.map(i => "$$" + i);
        this.metaMacro[name] = { inputs, output, from };
        const ast = parser.parse(inputs.join(",") + " ⊢M $$");
        for (const a of ast.nodes[0].nodes) {
            a.type = "rule";
        }
        ast.nodes[1].nodes[0].type = "rule";
        ast.nodes[1].nodes[0].name = ruleparser.stringify(output);
        this.addMetaRule(name, ast, inputs.map((e, i) => i), [], from);
    }
    _hasRpFn(m) {
        if (m.type === "fn" && m.name === "#rp") {
            return true;
        }
        if (!m.nodes)
            return false;
        for (const n of m.nodes) {
            if (this._hasRpFn(n))
                return true;
        }
        return false;
    }
    addHypothese(m, expandMode) {
        m = astmgr.clone(m);
        const astAssertions = {};
        assert.match(m, null, /^\$/, false, null, null, astAssertions, []);
        // assertions in condition can spread, i.e. fn(a,nf(a))  => fn(nf(a),nf(a))
        for (const astAss of Object.values(astAssertions)) {
            astmgr.replace(m, astAss.nodes[0], astAss);
        }
        assert.checkGrammer(m, "p");
        if (!expandMode && this._hasLocalNames(m))
            throw TR("假设中不能出现以#号开头的局部变量");
        try {
            assert.expand(m, false);
        }
        catch (e) {
            throw TR("假设中") + e;
        }
        if (!expandMode && this._hasRpFn(m))
            throw TR("假设中不能包含未化简的#rp函数，否则匹配机制将失效");
        this.propositions.push({ value: m, from: null });
        const dst = this.propositions.findIndex(e => e.from);
        if (dst !== -1) {
            this.moveProposition(this.propositions.length - 1, dst);
        }
        return this.propositions.length - 1;
    }
    // find #0 in ast
    _hasLocalNames(ast) {
        if (ast.type === "replvar" && ast.name.match(this.localNameRule)) {
            return true;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                if (this._hasLocalNames(n))
                    return true;
            }
        }
        return false;
    }
    // find ##0 in ast
    findLocalNamesInAst(ast, reg, res = new Set) {
        if (ast.type === "replvar" && ast.name.match(reg)) {
            res.add(ast.name);
            return res;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.findLocalNamesInAst(n, reg, res);
            }
        }
        return res;
    }
    // find ##0 in macro
    findLocalNamesInDeductionStep(steps, res = new Set) {
        if (!steps)
            return res;
        for (const step of steps) {
            for (const val of step.replaceValues) {
                this.findLocalNamesInAst(val, this.localReplacedNameRule, res);
                // Metadata belongs to this body. Referenced bodies are scoped
                // separately when expanded; never generate them during registration.
            }
        }
        return res;
    }
    replaceTempVar(ast, tempvarTable) {
        if (ast.type === "replvar" && ast.name.match(this.localNameRule)) {
            // ast.name = ast.name === "#" ? "##" : ast.name.replace(/^#([^#].*)$/, "##$1");
            while (tempvarTable.has(ast.name)) {
                if (ast.name === "#")
                    ast.name = "#0";
                else
                    ast.name += "#";
            }
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.replaceTempVar(n, tempvarTable);
            }
        }
    }
    // when inline, recover ##0 to #0. if outter has #0, change it to #0#
    recoverTempVar(ast, tempvarTable) {
        if (ast.type === "replvar" && ast.name.match(/^##.+$/)) {
            // special case: # -> ## -> ###
            ast.name = ast.name === "###" ? "#" : ast.name.replace(/^##(.+)$/, "#$1");
            while (tempvarTable.has(ast.name)) {
                ast.name += "#";
            }
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.recoverTempVar(n, tempvarTable);
            }
        }
    }
    addMacro(name, from) {
        const propositionIdx = this.propositions.length - 1;
        let hypothesisAmount = this.propositions.findIndex(e => e.from);
        if (hypothesisAmount == -1)
            hypothesisAmount = this.propositions.length;
        if (propositionIdx < hypothesisAmount)
            throw TR("无有效定理推导步骤，创建宏推导失败");
        const conditions = [];
        for (let i = 0; i < hypothesisAmount; i++) {
            conditions.push(this.propositions[i].value);
        }
        const conclusion = this.propositions[propositionIdx].value;
        if (this._hasLocalNames(conclusion)) {
            throw TR("局部变量不能出现在推理宏的结论中");
        }
        const macro = [];
        for (let i = hypothesisAmount; i <= propositionIdx; i++) {
            const step = this.propositions[i].from;
            macro.push({
                conditionIdxs: step.conditionIdxs.map(cidx => cidx < hypothesisAmount ? cidx : cidx - i),
                replaceValues: step.replaceValues.map(v => {
                    const newv = astmgr.clone(v);
                    return newv;
                }),
                deductionIdx: step.deductionIdx
            });
        }
        return this.addDeduction(name, {
            type: "meta", name: "⊢", nodes: [
                { type: "fn", name: "#array", nodes: conditions },
                { type: "fn", name: "#array", nodes: [conclusion] },
            ]
        }, from, macro);
    }
    removePropositions(amount) {
        if (!isFinite(amount)) {
            this.propositions = [];
        }
        else {
            while (amount--) {
                this.propositions.pop();
            }
        }
    }
    _getNewIndex(i, j, k) {
        if (k === i) {
            return j > i ? j - 1 : j;
        }
        if (i < j && k > i && k < j) {
            return k - 1;
        }
        if (i > j && k >= j && k < i) {
            return k + 1;
        }
        return k;
    }
    moveProposition(src, dst) {
        if (dst === -1)
            dst = this.propositions.length;
        if (src === dst || dst === src + 1)
            return;
        // 0 1 2 | 3 4 
        const hyps = this.propositions.findIndex(e => e.from);
        if (!this.propositions[src].from) {
            if (hyps !== -1 && dst > hyps) {
                const sv = this.propositions[src];
                sv.from = { conditionIdxs: [], replaceValues: [], deductionIdx: "" };
                try {
                    this.moveProposition(src, -1);
                    this.propositions.pop();
                }
                catch (e) {
                    delete sv.from;
                    throw TR("无法移动假设条件：假设须位于其它定理之前");
                }
                throw TR("被移动的假设条件被删除：假设须位于其它定理之前") + " - " + parser.stringify(sv.value);
            }
        }
        else if (dst < hyps) {
            throw TR("无法移动假设条件：假设须位于其它定理之前");
        }
        for (let i = Math.min(src, dst); i < this.propositions.length; i++) {
            const from = this.propositions[i]?.from;
            if (!from)
                continue;
            const ni = this._getNewIndex(src, dst, i);
            for (const j of from.conditionIdxs) {
                const nj = this._getNewIndex(src, dst, j);
                console.assert(nj !== ni);
                if (nj > ni)
                    throw TR("非法移动：推出定理") + "p" + i + TR("所依赖的定理") + "p" + j + TR("无法调整至其后方");
            }
        }
        for (let i = Math.min(src, dst); i < this.propositions.length; i++) {
            const from = this.propositions[i]?.from;
            if (!from)
                continue;
            from.conditionIdxs = from.conditionIdxs.map(e => this._getNewIndex(src, dst, e));
        }
        if (dst > src)
            dst--;
        const moved = this.propositions.splice(src, 1)[0];
        if (dst === this.propositions.length)
            this.propositions.push(moved);
        else
            this.propositions.splice(dst, 0, moved);
    }
    isNameCanBeNewConst(name) {
        if (assert.isConst(name))
            return `"${name}" ` + TR(`已有定义，无法重复定义`);
        this.consts.add(name);
        for (const [idx, d] of Object.entries(this.deductions)) {
            try {
                assert.checkGrammer(d.value, "d");
                assert.getReplVarsType(d.conclusion, {}, false);
            }
            catch (e) {
                this.consts.delete(name);
                return TR(`定义符号失败：`) + ` ${idx} : ` + e;
            }
        }
        for (const [idx, p] of this.propositions.entries()) {
            try {
                assert.checkGrammer(p.value, "p");
                assert.getReplVarsType(p.value, {}, false);
            }
            catch (e) {
                this.consts.delete(name);
                return TR(`定义符号失败：`) + ` p${idx} : ` + e;
            }
        }
        this.consts.delete(name);
        return true;
    }
    isNameCanBeNewFnOrVerb() {
        for (const [idx, d] of Object.entries(this.deductions)) {
            try {
                assert.checkGrammer(d.value, "d");
                assert.getReplVarsType(d.conclusion, {}, false);
            }
            catch (e) {
                throw TR(`定义符号失败：`) + ` ${idx} : ` + e;
            }
        }
        for (const [idx, p] of this.propositions.entries()) {
            try {
                assert.checkGrammer(p.value, "p");
                assert.getReplVarsType(p.value, {}, false);
            }
            catch (e) {
                throw TR(`定义符号失败：`) + ` p${idx} : ` + e;
            }
        }
        return true;
    }
    generateDeductionByToken(tree, name = ruleparser.stringify(tree)) {
        return this.evaluate(() => {
            if (this.generating.has(name))
                throw new Error("循环规则依赖 / Cyclic rule dependency: " + [...this.generating, name].join(" -> "));
            this.generating.add(name);
            this.generationDepth++;
            try {
                return this.generateDeductionByTokenChecked(tree, name);
            }
            finally {
                this.generationDepth--;
                this.generating.delete(name);
            }
        });
    }
    generateDeductionByTokenChecked(tree, name) {
        if (this.deductions[name])
            return this.deductions[name];
        const unlocked = this.fastmetarules;
        const from = "元规则生成*";
        const cmd = tree[0];
        const fn = {
            "<": this.metaInvDeductTheorem,
            ">": this.metaDeductTheorem,
            "c": this.metaConditionTheorem,
            "e": this.metaExistTheorem,
            "v": unlocked.includes("v") ? this.metaConditionUniversalTheorem : unlocked.includes("q") ? this.metaQuantifyAxiomSchema : null,
            "u": this.metaUniversalTheorem,
        }[tree[0]];
        if (fn) {
            if (!unlocked.includes(cmd) && cmd !== "v")
                throw "null";
            const subRuleName = ruleparser.stringify(tree[1]);
            this.generateDeductionByToken(tree[1], subRuleName);
            return this.deductions[fn.bind(this)(subRuleName, from)];
        }
        if (tree[0] === ":") {
            if (!unlocked.includes(":"))
                throw "null";
            let tempvar;
            const d1names = tree.slice(1).map(t => (tempvar = ruleparser.stringify(t),
                tempvar !== "#" ? this.generateDeductionByToken(t, tempvar) : null,
                tempvar));
            const d2name = d1names.pop();
            return this.deductions[this.metaCombineTheorem(d1names, d2name, from)];
        }
        if (tree.length === 1) {
            const dname = tree[0];
            let generated = null;
            if (unlocked.includes("#")) {
                generated ??= this.generateNatLiteralDef(dname);
                generated ??= this.generateNatLiteralIsNat(dname);
                generated ??= this.generateNatLiteralOp(dname);
            }
            if (unlocked.includes("z")) {
                generated ??= this.generateZLiteralDef(dname);
            }
            if (unlocked.includes("Z")) {
                generated ??= this.generateZLiteralIsZ(dname);
                generated ??= this.generateZLiteralOp(dname);
            }
            if (unlocked.includes("Q")) {
                generated ??= this.generateQLiteralDef(dname);
            }
            if (unlocked.includes("R")) {
                generated ??= this.generateRLiteralDef(dname);
            }
            if (generated)
                return this.deductions[generated];
        }
        throw "null";
    }
    getDeductionTokens(name) {
        return ruleparser.parse(name);
    }
    getAtomDeductionTokens(name, res = [], token = ruleparser.parse(name)) {
        if (token.length === 1) {
            res.push(token[0]);
        }
        else {
            for (let i = 1; i < token.length; i++)
                this.getAtomDeductionTokens("", res, token[i]);
        }
    }
    generateDeduction(name) {
        if (!name)
            return null;
        if (this.deductions[name])
            return this.deductions[name];
        // Bound parser recursion before entering RuleParser's recursive descent.
        if (name.length > 16_384)
            throw new Error("规则名称过长 / Rule expression too long");
        try {
            return this.evaluate(() => {
                const tokens = ruleparser.parse(name);
                return this.generateDeductionByToken(tokens);
            });
        }
        catch (e) {
            if (e === "null")
                return null;
            if (e === ",")
                throw TR(`使用元规则生成推理规则`) + name + TR(`时：意外出现了“,”`);
            throw TR(`使用元规则生成推理规则`) + name + TR(`时：`) + e;
        }
    }
    generateNatLiteralDef(name) {
        return this.generateLiteral(() => this.generateNatLiteralDefChecked(name));
    }
    generateNatLiteralDefChecked(name) {
        const n = name.match(/^d([1-9][0-9]+)$/);
        if (!n || !isFinite(Number(n[1])))
            return;
        if (this.deductions[name])
            return name;
        const num = BigInt(n[1]);
        return this.addDeduction(name, parser.parse(`⊢${num} =S(${num - 1n})`), "算数符号定义");
    }
    generateNatLiteralIsNat(name, vnum = 0) {
        return this.generateLiteral(() => this.generateNatLiteralIsNatChecked(name, vnum));
    }
    generateNatLiteralIsNatChecked(name, vnum = 0) {
        const vpre = "v".repeat(vnum);
        const n = name.match(/^\.([1-9][0-9]*)@N$/);
        if (!n || !isFinite(Number(n[1])))
            return;
        if (this.deductions[vpre + name])
            return vpre + name;
        const vars = [];
        let V = "";
        for (let i = 0; i < vnum; i++) {
            vars.push({ type: "replvar", name: "$" + i });
            V += "V$" + i + ":";
        }
        const num = BigInt(n[1]);
        const steps = [
            num === 1n ?
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "apn1" } :
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "." + (num - 1n) + "@N" },
            { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "apn2" },
            { conditionIdxs: [-1], replaceValues: [{ type: "replvar", name: String(num - 1n) }], deductionIdx: vpre + "<a4" },
            { conditionIdxs: [-1, -3], replaceValues: [], deductionIdx: vpre + "mp" },
            { conditionIdxs: [], replaceValues: [], deductionIdx: vpre + "d" + String(num) },
            { conditionIdxs: [-1], replaceValues: [], deductionIdx: vpre + ".=s" },
            { conditionIdxs: [-1, -3], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" }
        ];
        return this.addDeduction(vpre + name, parser.parse(`⊢${V}(${num}@N)`), "元规则生成*", steps, new Set());
    }
    generateNatLiteralOp(name, vnum = 0) {
        return this.generateLiteral(() => this.generateNatLiteralOpChecked(name, vnum));
    }
    generateNatLiteralOpChecked(name, vnum = 0) {
        const vpre = "v".repeat(vnum);
        const n = name.match(/^\.(0|[1-9][0-9]*)([\+\*])(0|[1-9][0-9]*)$/);
        if (!n || !isFinite(Number(n[1])) || !isFinite(Number(n[3])))
            return;
        if (this.deductions[vpre + name])
            return vpre + name;
        const vars = [];
        let V = "";
        for (let i = 0; i < vnum; i++) {
            vars.push({ type: "replvar", name: "$" + i });
            V += "V$" + i + ":";
        }
        const a = BigInt(n[1]);
        const b = BigInt(n[3]);
        const op = n[2];
        const isNat = (x) => {
            return x === 0n ? "apn1" : "." + x + "@N";
        };
        const steps = b === 0n ? [{ conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + ":" + isNat(a) + ",<d" + op + "1" }] : [
            b > 1n ?
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "." + a + op + (b - 1n) } :
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + ":" + isNat(a) + ",<d" + op + "1" },
            { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + ":" + isNat(a) + ",:" + isNat(b - 1n) + ",<<d" + op + "2" },
            { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "d" + b },
            op === "+" ? { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "d" + (a + b) } : b === 1n ? { conditionIdxs: [], replaceValues: [], deductionIdx: ":" + isNat(a) + ",<.0+" } :
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + `.${a * (b - 1n)}+${a}` },
            { conditionIdxs: [-4, -3], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" },
            op === "+" ? { conditionIdxs: [-2], replaceValues: [], deductionIdx: vpre + ".=s" } : null,
            { conditionIdxs: [op === "+" ? -4 : -3], replaceValues: [], deductionIdx: vpre + ".=s" },
            { conditionIdxs: [-1, op === "+" ? -3 : -2], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" },
            op === "+" ? { conditionIdxs: [-3, -1], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" } :
                { conditionIdxs: [-1, op === "+" ? -5 : -4], replaceValues: [], deductionIdx: vpre + ".=t" }
        ].filter(e => e);
        return this.addDeduction(vpre + name, parser.parse(`⊢${V}(${a}${op}${b}=${op === "+" ? a + b : a * b})`), "元规则生成*", steps, new Set());
    }
    generateZLiteralDef(name) {
        return this.generateLiteral(() => this.generateZLiteralDefChecked(name));
    }
    generateZLiteralDefChecked(name) {
        const n = name.match(/^dZ([\+\-])?([0-9]|[1-9][0-9]+)$/);
        if (!n)
            return;
        if (this.deductions[name])
            return name;
        const num = (n[1] ?? "+") + n[2];
        let pos = "0", min = "0";
        if (n[1] === "-") {
            min = n[2];
        }
        else {
            pos = n[2];
        }
        return this.addDeduction(name, parser.parse(`⊢${num} = Z((${pos},${min}))`), "算数符号定义");
    }
    generateZLiteralIsZ(name) {
        return this.generateLiteral(() => this.generateZLiteralIsZChecked(name));
    }
    generateZLiteralIsZChecked(name) {
        const n = name.match(/^\.([\+\-])?([0-9]|[1-9][0-9]+)@Z$/);
        if (!n)
            return;
        if (this.deductions[name])
            return name;
        const num = (n[1] ?? "+") + n[2];
        let pos = "apn1", min = "apn1";
        if (n[1] === "-") {
            min = Number(n[2]) !== 0 ? `.${n[2]}@N` : "apn1";
        }
        else {
            pos = Number(n[2]) !== 0 ? `.${n[2]}@N` : "apn1";
        }
        const steps = [
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:${pos}:${min},.@Z` },
            { conditionIdxs: [], replaceValues: [], deductionIdx: `dZ` + num },
            { conditionIdxs: [-1, -2], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: `:.=s,<<a8` },
        ];
        return this.addDeduction(name, parser.parse(`⊢(${num}@Z)`), "元规则生成*", steps, new Set());
    }
    generateZLiteralOp(name) {
        return this.generateLiteral(() => this.generateZLiteralOpChecked(name));
    }
    generateZLiteralOpChecked(name) {
        const n = name.match(/^\.([\+\-])?([0-9]|[1-9][0-9]+)([\+\-\*])([\+\-])?([0-9]|[1-9][0-9]+)$/);
        if (!n)
            return;
        if (this.deductions[name] || this.generateNatLiteralOp(name))
            return name;
        const num1 = (n[1] ?? "+") + n[2];
        let pos1 = "apn1", min1 = "apn1";
        let p11 = "0", p12 = "0";
        if (n[1] === "-") {
            min1 = Number(n[2]) !== 0 ? `.${n[2]}@N` : "apn1";
            p12 = n[2];
        }
        else {
            pos1 = Number(n[2]) !== 0 ? `.${n[2]}@N` : "apn1";
            p11 = n[2];
        }
        const num2 = (n[4] ?? "+") + n[5];
        let pos2 = "apn1", min2 = "apn1";
        let p21 = "0", p22 = "0";
        if (n[4] === "-") {
            min2 = Number(n[5]) !== 0 ? `.${n[5]}@N` : "apn1";
            p22 = n[5];
        }
        else {
            pos2 = Number(n[5]) !== 0 ? `.${n[5]}@N` : "apn1";
            p21 = n[5];
        }
        const num3 = n[3] === "+" ? BigInt(num1) + BigInt(num2) : n[3] === "-" ? BigInt(num1) - BigInt(num2) : BigInt(num1) * BigInt(num2);
        const writeValue = (...v) => v.map(e => ({ type: "replvar", name: e }));
        const _0 = [{ type: "replvar", name: "0" }];
        const a8 = { conditionIdxs: [-1, -2], replaceValues: _0, deductionIdx: `<<a8` };
        const steps = [
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:${pos1}:${min1},.Xi` },
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:${pos2}:${min2},.Xi` },
            { conditionIdxs: [-2, -1], replaceValues: [], deductionIdx: `<<dZ` + n[3] },
            { conditionIdxs: [], replaceValues: writeValue(p11, p12), deductionIdx: `:.Pr1,.=s` }, a8,
            { conditionIdxs: [], replaceValues: writeValue(p21, p22), deductionIdx: `:.Pr1,.=s` }, a8,
            { conditionIdxs: [], replaceValues: writeValue(p11, p12), deductionIdx: `:.Pr2,.=s` }, a8,
            { conditionIdxs: [], replaceValues: writeValue(p21, p22), deductionIdx: `:.Pr2,.=s` }, a8,
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:dZ${num1},.=s` }, a8,
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:dZ${num2},.=s` }, a8,
            { conditionIdxs: [], replaceValues: [], deductionIdx: n[3] === "+" ? `.${p11}+${p21}` : n[3] === "*" ? `.${p11}*${p21}` : `.${p11}+${p22}` }, a8,
            { conditionIdxs: [], replaceValues: [], deductionIdx: n[3] === "+" ? `.${p12}+${p22}` : n[3] === "*" ? `.${p12}*${p22}` : `.${p12}+${p21}` }, a8,
        ];
        let a = n[3] === "+" ? BigInt(p11) + BigInt(p21) : BigInt(p11) + BigInt(p22);
        let b = n[3] === "+" ? BigInt(p12) + BigInt(p22) : BigInt(p12) + BigInt(p21);
        if (n[3] === "*") {
            steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${p11}*${p22}` }, a8);
            steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${p12}*${p21}` }, a8);
            const x11_21 = BigInt(p11) * BigInt(p21);
            const x12_22 = BigInt(p12) * BigInt(p22);
            const x11_22 = BigInt(p11) * BigInt(p22);
            const x21_12 = BigInt(p21) * BigInt(p12);
            steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${x11_21}+${x12_22}` }, a8);
            steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${x11_22}+${x21_12}` }, a8);
            a = x11_21 + x12_22;
            b = x11_22 + x21_12;
        }
        if (a > 0n && b > 0n) {
            if (a >= b) {
                const a_min_b = a - b;
                const a_min_bN = a_min_b === 0n ? "apn1" : `.${a_min_b}@N`;
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `:${a_min_bN}:apn1:.${b}@N,.Zr` });
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${a_min_b}+${b}` }, a8);
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.0+${b}` }, a8);
            }
            else {
                const b_min_a = b - a;
                const b_min_aN = `.${b_min_a}@N`;
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `:apn1:${b_min_aN}:.${a}@N,.Zr` });
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.0+${a}` }, a8);
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${b_min_a}+${a}` }, a8);
            }
        }
        steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `dZ` + num3 });
        if (a > 0n && b > 0n)
            steps.push({ conditionIdxs: [-1, -2], replaceValues: [], deductionIdx: `.=t` });
        steps.push({ conditionIdxs: [n[3] === "*" ? -2 : (18 - steps.length), -1], replaceValues: [], deductionIdx: `:#:.=s,.=t` });
        return this.addDeduction(name, parser.parse(`⊢(${num1}${n[3]}${num2}=${num3 >= 0n ? "+" + num3 : num3})`), "元规则生成*", steps, new Set());
    }
    generateQLiteralDef(name) {
        return this.generateLiteral(() => this.generateQLiteralDefChecked(name));
    }
    generateQLiteralDefChecked(name) {
        let n = name.match(/^dQ([\+\-])?([0-9]|[1-9][0-9]+)q?$/) || name.match(/^d([\+\-])?([0-9]|[1-9][0-9]+)q$/);
        if (this.deductions[name])
            return name;
        if (n) {
            const num = (n[1] === "-" ? "-" : "") + n[2];
            return this.addDeduction(name, parser.parse(`⊢${num}q = Q((${(n[1] ?? "+") + n[2]},+1))`), "算数符号定义");
        }
        n = name.match(/^dQ?([\+\-])?([0-9]|[1-9][0-9]+)\.([0-9]*)q?$/);
        if (!n)
            return;
        const [_, sym, a, b] = n;
        const num = (sym === "-" ? "-" : "") + a + "." + b;
        const int = a + b;
        return this.addDeduction(name, parser.parse(`⊢${num} = Q((${(n[1] ?? "+") + (int.replace(/^0*/, "") ?? "0")},+1${"0".repeat(b.length)}))`), "算数符号定义");
    }
    generateRLiteralDef(name) {
        return this.generateLiteral(() => this.generateRLiteralDefChecked(name));
    }
    generateRLiteralDefChecked(name) {
        let n = name.match(/^dR([\+\-])?([0-9]|[1-9][0-9]+)r?$/) || name.match(/^d([\+\-])?([0-9]|[1-9][0-9]+)r$/);
        if (this.deductions[name])
            return name;
        if (n) {
            const num = (n[1] === "-" ? "-" : "") + n[2];
            return this.addDeduction(name, parser.parse(`⊢${num}r = {x@Q|x<=${num}&~x=${num}}`), "算数符号定义");
        }
        n = name.match(/^dR?([\+\-])?([0-9]|[1-9][0-9]+)\.([0-9]*)r?$/);
        if (!n)
            return;
        const [_, sym, a, b] = n;
        const num = (sym === "-" ? "-" : "") + a + "." + b;
        return this.addDeduction(name, parser.parse(`⊢${num}r = {x@Q|x<=${num}&~x=${num}}`), "算数符号定义");
    }
    deduct(step, inlineMode, partialTest) {
        return this.evaluate(() => {
            const stack = [{ rule: step.deductionIdx, expanding: !!inlineMode, iterator: this.deductChecked(step, inlineMode, partialTest) }];
            const active = new Set(inlineMode ? [step.deductionIdx] : []);
            let result;
            while (stack.length) {
                this.evaluation.check();
                const frame = stack[stack.length - 1];
                const next = frame.iterator.next(result);
                if (next.done) {
                    result = next.value;
                    if (frame.expanding)
                        active.delete(frame.rule);
                    stack.pop();
                }
                else {
                    const child = next.value;
                    if (child.mode && active.has(child.step.deductionIdx))
                        throw new Error("循环证明依赖 / Cyclic proof dependency: " + child.step.deductionIdx);
                    if (child.mode)
                        active.add(child.step.deductionIdx);
                    stack.push({ rule: child.step.deductionIdx, expanding: !!child.mode, iterator: this.deductChecked(child.step, child.mode) });
                    result = undefined;
                }
            }
            return result;
        });
    }
    *deductChecked(step, inlineMode, partialTest) {
        const { conditionIdxs, deductionIdx, replaceValues } = step;
        const deduction = this.generateDeduction(deductionIdx);
        const errorMsg = TR(`规则 `) + deductionIdx + TR(` 推理失败:`);
        if (!deduction)
            throw errorMsg + TR("规则不存在");
        const { conditions, conclusion, replaceNames, replaceTypes } = deduction;
        // firstly, match condition, get matchtable ( partial initially provided by users)
        let replacedVarTypeTable = {};
        let matchTable = partialTest ? {} : Object.fromEntries(replaceNames.map((replname, idx) => (assert.getReplVarsType(replaceValues[idx], replacedVarTypeTable, replaceTypes[replname]),
            [replname, astmgr.clone(replaceValues[idx])])));
        // assertions in pattern
        let assertions = [];
        let assertionsFrom = [];
        // assertions in matched conditions
        let astAssertions = {};
        for (const [conditionIdx, condition] of conditions.entries()) {
            const condPropIdx = conditionIdxs[conditionIdx];
            if (partialTest && !isFinite(condPropIdx))
                return;
            const condProp = this.propositions[condPropIdx];
            if (!condProp)
                throw errorMsg + TR(`第${conditionIdx + 1}个`) + TR(`条件对应的定理p`) + condPropIdx + TR(`不存在`);
            try {
                // 
                assert.match(condProp.value, condition, /^\$/, false, matchTable, replacedVarTypeTable, null, assertions);
                while (assertionsFrom.length < assertions.length)
                    assertionsFrom.push(conditionIdx);
            }
            catch (e) {
                // match failed
                throw errorMsg + TR(`第${conditionIdx + 1}个`) + TR(`条件`) + e;
            }
        }
        replaceNames.forEach((replname, idx) => {
            const nast = astmgr.clone(replaceValues[idx]);
            assert.expand(nast, replaceTypes[replname]);
            assert.match(nast, null, /^\$/, replaceTypes[replname], null, null, astAssertions, assertions);
        });
        if (partialTest)
            return; // just test, no props to add
        // assertions in condition can spread, i.e. fn(a,nf(a))  => fn(nf(a),nf(a))
        // we spread it over matchTable and pattern assertions
        for (const astAss of Object.values(astAssertions)) {
            for (const ass of assertions) {
                astmgr.replace(ass, astAss.nodes[0], astAss);
            }
            for (const [n, v] of Object.entries(matchTable)) {
                astmgr.replace(v, astAss.nodes[0], astAss);
            }
        }
        // then replace replvars in assertions by matchtable, and check them
        for (const [idx, ass] of assertions.entries()) {
            const cas = astmgr.clone(ass);
            astmgr.replaceByMatchTable(cas, matchTable);
            // todo: how to get assert's type
            try {
                assert.assertUnwrap(cas, replacedVarTypeTable);
            }
            catch (e) {
                // assertion in condition failed (first layer must be T)
                throw errorMsg + TR(`第${assertionsFrom[idx] + 1}个`) + TR(`条件中:`) + e;
            }
        }
        // finally replace conclusion
        let replacedConclusion = astmgr.clone(conclusion);
        // to prevent #nf inconsist in conclusion, we record replaceVals
        astmgr.replaceByMatchTable(replacedConclusion, matchTable);
        try {
            assert.checkGrammer(replacedConclusion, "p");
            // grammar in conclusion failed
        }
        catch (e) {
            throw TR("结论中出现语法错误：") + e;
        }
        try {
            assert.expand(replacedConclusion, false);
        }
        catch (e) {
            // assertion in conclusion failed (can be T or U, only F to fail)
            throw errorMsg + TR(`结论中：`) + e;
        }
        // if it isn't macro or not inineMode, done
        let netInlineMode = inlineMode;
        if (typeof netInlineMode === "function")
            netInlineMode = netInlineMode(step, replacedConclusion);
        if (!netInlineMode || !this.hasProofSteps(deduction)) {
            return this.propositions.push({ value: replacedConclusion, from: step }) - 1;
        }
        // if it is macro and inline, expand substeps 
        const steps = this.getProofSteps(deduction);
        const stepOutputs = [];
        // find outter tempvars
        let tempvars = new Set;
        Object.values(matchTable).forEach(v => this.findLocalNamesInAst(v, this.localNameRule, tempvars));
        for (const [substepIdx, substep] of steps.entries()) {
            // if condition number is positive, use given macro condition props
            // if condition number is negative, this implies newly deducted props, which is relative to the end of prop list
            const replacedConditionIdxs = substep.conditionIdxs.map(idx => {
                if (idx >= 0)
                    return conditionIdxs[idx];
                return stepOutputs[substepIdx + idx];
            });
            const replaceValues = substep.replaceValues.map(ast => {
                const replaced = astmgr.clone(ast);
                this.replaceTempVar(replaced, tempvars);
                // this.replaceTempVar
                astmgr.replaceByMatchTable(replaced, matchTable);
                return replaced;
            });
            const lastPos = yield { step: { deductionIdx: substep.deductionIdx, replaceValues, conditionIdxs: replacedConditionIdxs }, mode: netInlineMode === "deep" ? inlineMode : null };
            stepOutputs.push(lastPos);
        }
        const propLength = this.propositions.length;
        if (!astmgr.equal(this.propositions[propLength - 1]?.value, replacedConclusion)) {
            throw new Error("展开结果与规则结论不一致 / Expanded proof does not match the rule conclusion: " + deductionIdx);
        }
        return propLength - 1;
    }
    expandMacroWithProp(propositionIdx) {
        return this.evaluate(() => this.expandMacroWithPropChecked(propositionIdx));
    }
    expandMacroWithPropChecked(propositionIdx) {
        const p = this.propositions[propositionIdx];
        if (!p.from)
            throw TR("该定理为假设，无推理步骤可展开");
        const { deductionIdx, conditionIdxs, replaceValues } = p.from;
        if (!this.deductions[deductionIdx])
            this.deductions[deductionIdx] = this.generateDeduction(deductionIdx);
        const from = this.deductions[deductionIdx].from;
        if (!this.isMacro(this.deductions[deductionIdx]))
            throw TR(`该定理由来自<`) + TR(deductionIdx[0] === "v" ? TR("一阶逻辑公理模式") : from) + TR(`>的原子推理规则得到，无子步骤`);
        const hyps = conditionIdxs.map(c => this.propositions[c].value);
        this.removePropositions();
        // expandMode set true to skip local var check in addHypothese
        hyps.forEach(h => this.addHypothese(h, true));
        this.deduct({
            deductionIdx, conditionIdxs: hyps.map((v, idx) => idx), replaceValues
        }, "inline");
    }
    inlineMacroInProp(propositionIdx) {
        return this.evaluate(() => this.inlineMacroInPropChecked(propositionIdx));
    }
    inlineMacroInPropChecked(propositionIdx) {
        const p = this.propositions[propositionIdx];
        if (!p.from)
            throw TR("该定理为假设，无推理步骤可展开");
        const { deductionIdx, conditionIdxs, replaceValues } = p.from;
        if (!this.deductions[deductionIdx])
            this.deductions[deductionIdx] = this.generateDeduction(deductionIdx);
        if (!this.isMacro(this.deductions[deductionIdx]))
            throw TR(`该定理由来自<`) + TR(this.deductions[deductionIdx].from) + TR(`>的原子推理规则得到，无子步骤`);
        const suivant = [];
        while (true) {
            const p1 = this.propositions.pop();
            if (p1 !== p)
                suivant.unshift(p1);
            if (p1 === p) {
                break;
            }
        }
        const before = this.propositions.length;
        this.deduct({
            deductionIdx, conditionIdxs, replaceValues
        }, "inline");
        const offset = this.propositions.length - before - 1;
        while (true) {
            const p1 = suivant.shift();
            if (!p1)
                break;
            if (!p1.from)
                continue;
            this.evaluation.check();
            this.propositions.push({ ...p1, from: { ...p1.from,
                    conditionIdxs: p1.from.conditionIdxs.map(id => id < propositionIdx ? id : id + offset)
                } });
        }
    }
    expandMacroWithDefaultValue(deductionIdx, inlineMode = "inline", expandAxiom) {
        return this.evaluate(() => this.expandMacroWithDefaultValueChecked(deductionIdx, inlineMode, expandAxiom));
    }
    expandMacroWithDefaultValueChecked(deductionIdx, inlineMode = "inline", expandAxiom) {
        const d = this.deductions[deductionIdx] || this.generateDeduction(deductionIdx);
        if (!d)
            throw TR(`推理规则 `) + deductionIdx + TR(` 不存在`);
        if (!expandAxiom && !this.isMacro(d))
            throw TR(`无法展开原子推理规则`);
        this.removePropositions();
        d.conditions.forEach(dcond => this.addHypothese(dcond));
        this.deduct({
            deductionIdx, conditionIdxs: d.conditions.map((v, idx) => idx),
            replaceValues: d.replaceNames.map(str => ({ type: "replvar", name: str }))
        }, inlineMode);
    }
    _findReplNameInRule(deductionIdx) {
        const d = this.deductions[deductionIdx];
        const p = new Set;
        for (const c of d.conditions)
            astmgr.getVarNames(c, p, /^\$/);
        astmgr.getVarNames(d.conclusion, p, /^\$/);
        return p;
    }
    _findNewReplName(deductionIdx, p = new Set) {
        let name = "$0", i = 0;
        if (deductionIdx) {
            const d = this.deductions[deductionIdx];
            if (!d)
                throw TR("无法生成中间步骤推理规则：") + deductionIdx;
            for (const c of d.conditions)
                astmgr.getVarNames(c, p, /^\$/);
            astmgr.getVarNames(d.conclusion, p, /^\$/);
        }
        while (p.has(name)) {
            name = "$" + (i++);
        }
        return { type: "replvar", name };
    }
    metaQuantifyAxiomSchema(deductionIdx, from) {
        return this.generateRule(() => this.metaQuantifyAxiomSchemaChecked(deductionIdx, from));
    }
    metaQuantifyAxiomSchemaChecked(deductionIdx, from) {
        const d = this.generateDeduction(deductionIdx);
        if (!d)
            throw TR(`推理规则 `) + deductionIdx + TR(` 不存在`);
        if (d.conditions?.length)
            throw TR("无法匹配带条件的推理规则");
        if (this.hasProofSteps(d))
            throw TR("无法匹配非公理推理规则");
        if (this.deductions["v" + deductionIdx])
            return "v" + deductionIdx;
        return this.addDeduction("v" + deductionIdx, {
            type: "meta", name: "⊢",
            nodes: [
                { type: "fn", name: "#array", nodes: [] },
                {
                    type: "fn", name: "#array", nodes: [
                        {
                            type: "sym", name: "V", nodes: [
                                this._findNewReplName(deductionIdx),
                                d.conclusion
                            ]
                        }
                    ]
                },
            ]
        }, from);
    }
    metaExistTheorem(idx, from) {
        return this.generateRule(() => this.metaExistTheoremChecked(idx, from));
    }
    metaExistTheoremChecked(idx, from) {
        const d = this.generateDeduction(idx);
        if (d.conditions.length !== 1)
            throw TR("匹配条件推理规则($$0 ⊢ $$1)失败");
        if (this.deductions["e" + idx])
            return "e" + idx;
        const oldP = this.propositions;
        try {
            this.removePropositions();
            const s = this._findNewReplName(idx);
            let pidx = 0;
            // |- Ea   |- v(a>b)  |- Ea > Eb
            this.addHypothese({
                type: "sym", name: "E", nodes: [
                    s, d.conditions[0]
                ]
            });
            pidx++;
            const vd = this.generateDeduction(("v>" + idx).replace("><", ""));
            this.deduct({
                deductionIdx: ("v>" + idx).replace("><", ""),
                replaceValues: vd.replaceNames.map(e => ({ type: "replvar", name: e })),
                conditionIdxs: []
            });
            pidx++;
            this.deduct({
                deductionIdx: ".Emp",
                replaceValues: [],
                conditionIdxs: [1, 0]
            });
            pidx++;
            const ret = this.addMacro("e" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaConditionUniversalTheorem(idx, from) {
        return this.generateRule(() => this.deferLift("v", idx, from, () => this.metaConditionUniversalTheoremChecked(idx, from)));
    }
    metaConditionUniversalTheoremChecked(idx, from) {
        // mp
        if (this.deductions["v" + idx])
            return "v" + idx;
        const num = idx.match(/^(v*)/)?.[1]?.length;
        if (num >= 0 && this.generateNatLiteralOp(idx.slice(num), 1 + num)) {
            return "v" + idx;
        }
        const d = this.generateDeduction(idx);
        const s = this._findNewReplName(idx);
        const SmatchTable = { [s.name]: { type: "replvar", name: "#" + s.name } };
        // axiom
        if (!this.hasProofSteps(d) && !d.conditions?.length) {
            return this.metaQuantifyAxiomSchema(idx, "元规则生成*");
        }
        const steps = this.getProofSteps(d);
        // macro
        const offsetTable = [];
        const offsetCondTable = [];
        const generate = (condMode, idx) => {
            this.evaluation.enter();
            try {
                return generateChecked(condMode, idx);
            }
            finally {
                this.evaluation.leave();
            }
        };
        const generateChecked = (condMode, idx) => {
            idx ??= steps.length - 1 + d.conditions.length;
            const step = steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            const stepReplaceValues = step?.replaceValues?.map(e => {
                const rv = astmgr.clone(e);
                astmgr.replaceByMatchTable(rv, SmatchTable);
                return rv;
            });
            if (!condMode) {
                // avoid repeated deductions on the same prop (here reaching hyps are not possible)
                if (isFinite(offsetTable[idx]))
                    return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: stepReplaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx]))
                return offsetCondTable[idx];
            if (!sd)
                throw TR("无法生成中间步骤推理规则：") + sdidx;
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: this.metaConditionUniversalTheorem(sdidx, ""),
                replaceValues: sd.conditions.length ? stepReplaceValues : [s, ...stepReplaceValues],
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        };
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                this.addHypothese({ type: "sym", name: "V", nodes: [s, c] });
                offsetCondTable.push(id);
            });
            generate(true);
            const ret = this.addMacro("v" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaUniversalTheorem(idx, from) {
        return this.generateRule(() => this.metaUniversalTheoremChecked(idx, from));
    }
    metaUniversalTheoremChecked(idx, from) {
        if (this.deductions["u" + idx])
            return "u" + idx;
        const d = this.generateDeduction(idx);
        if (!d)
            throw TR("条件中的推理规则不存在");
        if (!d.conditions.length) {
            this.metaConditionUniversalTheorem(idx, from);
            this.deductions["u" + idx] = this.deductions["v" + idx];
            return "u" + idx;
        }
        const s = this._findNewReplName(idx);
        for (const [idx, cond] of d.conditions.entries()) {
            if (assert.nf(s.name, cond) === -1) {
                throw TR(`元推理结论规则中的条件中的#nf函数永远无法通过验证`);
            }
        }
        const steps = this.getProofSteps(d);
        // macro
        const offsetTable = [];
        const offsetCondTable = [];
        // find wrappers (e.g. #nf #vnf ..) for replvars in condition
        const replvarTable = {};
        const generate = (condMode, idx) => {
            this.evaluation.enter();
            try {
                return generateChecked(condMode, idx);
            }
            finally {
                this.evaluation.leave();
            }
        };
        const generateChecked = (condMode, idx) => {
            idx ??= steps.length - 1 + d.conditions.length;
            const step = steps[idx - d.conditions.length];
            // step may not exists, e.g. hyp
            const stepReplaceValues = step?.replaceValues?.map(v => {
                const cv = astmgr.clone(v);
                astmgr.replaceByMatchTable(cv, replvarTable);
                return cv;
            });
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop (here reaching hyps are not possible)
                if (isFinite(offsetTable[idx]))
                    return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: stepReplaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx]))
                return offsetCondTable[idx];
            if (!sd)
                throw TR("无法生成中间步骤推理规则：") + sdidx;
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: this.metaConditionUniversalTheorem(sdidx, "元规则生成*"),
                replaceValues: sd.conditions.length ? stepReplaceValues : [s, ...stepReplaceValues],
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        };
        const oldP = this.propositions;
        const fastrules = this.fastmetarules;
        this.fastmetarules += "<";
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                const newHyp = { type: "fn", name: "#nf", nodes: [c, s] };
                this.addHypothese(newHyp);
                try {
                    assert.match(this.propositions[id].value, c, /^\$/, false, replvarTable, {}, null, []);
                }
                catch (e) {
                    throw TR(`向`) + TR(`第${id + 1}个`) + TR(`条件添加不自由断言时出现不一致：`) + e;
                }
            });
            d.conditions.forEach((c, id) => {
                // const p0 = this.deduct({ deductionIdx: "a6", replaceValues: [this.propositions[id].value, s], conditionIdxs: [] });
                const p1 = this.deduct({ deductionIdx: "<a6", conditionIdxs: [id], replaceValues: [s] });
                offsetCondTable[id] = p1;
            });
            replvarTable[s.name] = { type: "replvar", name: "#" + s.name };
            generate(true);
            const ret = this.addMacro("u" + idx, from);
            this.propositions = oldP;
            this.fastmetarules = fastrules;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            this.fastmetarules = fastrules;
            throw e;
        }
    }
    metaNewConstant(replaceValues, from) {
        return this.evaluate(() => this.metaNewConstantChecked(replaceValues, from));
    }
    metaNewConstantChecked(replaceValues, from) {
        this.invalidateGenerated();
        const [constAst, varAst, exprAst] = replaceValues;
        if (constAst.type !== "replvar")
            throw TR("$$0只能为纯变量名");
        if (constAst.name.match(/[A-Z]/))
            throw TR(`自定义符号中不能有大写字母`);
        if (constAst.name.startsWith("$"))
            throw TR("以$开头的变量名称被系统保留");
        if (constAst.name.startsWith("#"))
            throw TR("以#开头的变量名称被系统保留");
        const constCheckRes = this.isNameCanBeNewConst(constAst.name);
        if (constCheckRes !== true)
            throw TR("匹配条件##newconst($$0)时：") + constCheckRes;
        if (this.fns.has(constAst.name))
            throw TR("匹配条件##newconst($$0)时：$$0已有定义");
        const deduction = astmgr.clone(this.metaRules["c"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": constAst,
            "$$1": varAst,
            "$$2": exprAst
        };
        astmgr.replaceByMatchTable(deduction, replTable);
        if (assert.nf(constAst.name, exprAst) !== 1)
            throw TR("检测到可能的循环定义");
        const R = astmgr.clone(exprAst);
        astmgr.replace(R, varAst, constAst);
        const freeVars = new Set;
        assert.getFreeVars(exprAst, freeVars);
        if (Array.from(freeVars).find(e => e !== varAst.name && !assert.isConst(e))) {
            throw TR("表达式不能有自由变量");
        }
        if (assert.nf(constAst.name, R) !== -1)
            throw TR("定义的常量没在结论中出现");
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1], R);
        let d;
        try {
            this.consts.add(constAst.name);
            d = this.addDeduction("dc" + constAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length)
                throw TR("不能包含$开头的替代项");
        }
        catch (e) {
            if (d)
                delete this.deductions[d];
            this.consts.delete(constAst.name);
            throw e;
        }
        return d;
    }
    metaNewFunction(replaceValues, from) {
        return this.evaluate(() => this.metaNewFunctionChecked(replaceValues, from));
    }
    metaNewFunctionChecked(replaceValues, from) {
        this.invalidateGenerated();
        const [fnAst, varAst, exprAst, paramAsts] = replaceValues;
        if (!paramAsts.length)
            throw null;
        if (fnAst.type !== "replvar")
            throw TR("$$0只能为纯变量名");
        if (fnAst.name.match(/[A-Z]/))
            throw TR(`自定义符号中不能有大写字母`);
        if (fnAst.name.startsWith("#"))
            throw TR("以#开头的函数被系统保留");
        if (fnAst.name.startsWith("$"))
            throw TR("以$开头的函数被系统保留");
        const fnCheckRes = this.fns.has(fnAst.name) || this.verbs.has(fnAst.name);
        if (fnCheckRes)
            throw TR(`匹配条件##newfn($$0)时：$$0已有定义`);
        const deduction = astmgr.clone(this.metaRules["f"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": fnAst,
            "$$2": varAst,
            "$$3": exprAst
        };
        const circularDetect = (ast) => {
            if (ast.type === "fn" && ast.name === fnAst.name && ast.nodes?.length === paramAsts.length)
                return true;
            for (let i = 0; i < ast.nodes?.length; i++) {
                if (circularDetect(ast.nodes[i]))
                    return true;
            }
            return false;
        };
        if (circularDetect(exprAst))
            throw TR("检测到可能的循环定义");
        const wrapVs = (ast) => {
            const freeVars = new Set;
            assert.getFreeVars(exprAst, freeVars);
            if (Array.from(freeVars).find(e => e !== varAst.name && !paramAsts.find(p => p.name === e) && !assert.isConst(e))) {
                throw TR("表达式不能有自由变量");
            }
            console.assert(ast.name === "V");
            let first = true;
            for (const p of paramAsts) {
                const n = p.name;
                if (p.type !== "replvar")
                    throw TR("函数的参数必须是变量");
                if (assert.isConst(n))
                    throw TR("函数的参数不能是常量");
                if (first) {
                    astmgr.assign(ast.nodes[0], p);
                    first = false;
                    continue;
                }
                astmgr.assign(ast, { type: "sym", name: "V", nodes: [p, ast] });
            }
        };
        astmgr.replaceByMatchTable(deduction, replTable);
        const R = astmgr.clone(exprAst);
        if (assert.nf(varAst.name, R) !== -1)
            throw TR("定义的函数表达式没在结论中出现");
        astmgr.replace(R, varAst, { type: "fn", name: fnAst.name, nodes: paramAsts });
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1].nodes[1], R);
        wrapVs(deduction.nodes[1].nodes[0].nodes[0]);
        wrapVs(deduction.nodes[1].nodes[0].nodes[1]);
        let d;
        try {
            this.fns.add(fnAst.name);
            this.isNameCanBeNewFnOrVerb();
            d = this.addDeduction("df" + fnAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length)
                throw TR("不能包含$开头的替代项");
        }
        catch (e) {
            if (d)
                delete this.deductions[d];
            this.fns.delete(fnAst.name);
            throw e;
        }
        return d;
    }
    metaNewVerb(replaceValues, from) {
        return this.evaluate(() => this.metaNewVerbChecked(replaceValues, from));
    }
    metaNewVerbChecked(replaceValues, from) {
        this.invalidateGenerated();
        const [fnAst, exprAst, paramAsts] = replaceValues;
        if (!paramAsts.length)
            throw null;
        if (fnAst.type !== "replvar")
            throw TR("$$0只能为纯变量名");
        if (fnAst.name.match(/[A-Z]/))
            throw TR(`自定义符号中不能有大写字母`);
        if (fnAst.name.startsWith("#"))
            throw TR("以#开头的函数被系统保留");
        if (fnAst.name.startsWith("$"))
            throw TR("以$开头的函数被系统保留");
        const fnCheckRes = this.fns.has(fnAst.name) || this.verbs.has(fnAst.name);
        if (fnCheckRes)
            throw TR(`匹配条件##newfn($$0)时：$$0已有定义`);
        const deduction = astmgr.clone(this.metaRules["prd"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": fnAst,
            "$$2": exprAst
        };
        const circularDetect = (ast) => {
            if (ast.type === "fn" && ast.name === fnAst.name && ast.nodes?.length === paramAsts.length)
                return true;
            for (let i = 0; i < ast.nodes?.length; i++) {
                if (circularDetect(ast.nodes[i]))
                    return true;
            }
            return false;
        };
        if (circularDetect(exprAst))
            throw TR("检测到可能的循环定义");
        const wrapVs = (ast) => {
            console.assert(ast.name === "V");
            let first = true;
            for (const p of paramAsts) {
                const n = p.name;
                if (p.type !== "replvar")
                    throw TR("函数的参数必须是变量");
                if (assert.isConst(n))
                    throw TR("函数的参数不能是常量");
                if (first) {
                    astmgr.assign(ast.nodes[0], p);
                    first = false;
                    continue;
                }
                astmgr.assign(ast, { type: "sym", name: "V", nodes: [p, ast] });
            }
        };
        astmgr.replaceByMatchTable(deduction, replTable);
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1].nodes[0], { type: "fn", name: fnAst.name, nodes: paramAsts });
        wrapVs(deduction.nodes[1].nodes[0]);
        let d;
        try {
            this.verbs.add(fnAst.name);
            this.isNameCanBeNewFnOrVerb();
            d = this.addDeduction("dv" + fnAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length)
                throw TR("不能包含$开头的替代项");
        }
        catch (e) {
            if (d)
                delete this.deductions[d];
            this.verbs.delete(fnAst.name);
            throw e;
        }
        return d;
    }
    _replaceFnName(ast, src, dst) {
        if (ast.type === "fn" && ast.name === src) {
            ast.name = dst;
            return;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this._replaceFnName(n, src, dst);
            }
        }
    }
    metaConditionTheorem(idx, from) {
        return this.generateRule(() => this.deferLift("c", idx, from, () => this.metaConditionTheoremChecked(idx, from)));
    }
    metaConditionTheoremChecked(idx, from) {
        // mp
        if (this.deductions["c" + idx])
            return "c" + idx;
        const d = this.generateDeduction(idx);
        const s = this._findNewReplName(idx);
        const fastrule = this.fastmetarules;
        this.fastmetarules += "<";
        // axiom, |- A
        if (!d.conditions.length) {
            const oldP = this.propositions;
            try {
                this.expandMacroWithDefaultValue(idx, null, true);
                this.deduct({
                    deductionIdx: "<a1", conditionIdxs: [0],
                    replaceValues: [s]
                });
                const ret = this.addMacro("c" + idx, from);
                this.propositions = oldP;
                this.fastmetarules = fastrule;
                return ret;
            }
            catch (e) {
                this.propositions = oldP;
                this.fastmetarules = fastrule;
                throw e;
            }
        }
        // ...A |- B
        const offsetTable = [];
        const offsetCondTable = [];
        const steps = this.getProofSteps(d);
        const generate = (condMode, idx) => {
            this.evaluation.enter();
            try {
                return generateChecked(condMode, idx);
            }
            finally {
                this.evaluation.leave();
            }
        };
        const generateChecked = (condMode, idx) => {
            idx ??= steps.length - 1 + d.conditions.length;
            const step = steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop (here reaching hyps are not possible)
                if (isFinite(offsetTable[idx]))
                    return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: step.replaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx]))
                return offsetCondTable[idx];
            if (!sd.conditions.length) {
                const p0 = generate(false, idx);
                return offsetCondTable[idx] = this.deduct({
                    deductionIdx: "<a1", conditionIdxs: [p0],
                    replaceValues: [s]
                });
            }
            this.metaConditionTheorem(sdidx, "中间步骤");
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: "c" + sdidx, replaceValues: step.replaceValues,
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        };
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                this.addHypothese({ type: "sym", name: ">", nodes: [s, c] });
                offsetCondTable.push(id);
            });
            generate(true);
            const ret = this.addMacro("c" + idx, from);
            this.propositions = oldP;
            this.fastmetarules = fastrule;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            this.fastmetarules = fastrule;
            throw e;
        }
    }
    metaDeductTheorem(idx, from) {
        return this.generateRule(() => this.metaDeductTheoremChecked(idx, from));
    }
    metaDeductTheoremChecked(idx, from) {
        if (idx[0] === "<") {
            this.generateDeduction(idx.slice(1));
            return idx.slice(1);
        }
        if (this.deductions[">" + idx])
            return ">" + idx;
        const d = this.generateDeduction(idx);
        const fastrule = this.fastmetarules;
        // mp, axiom, |- A : error
        if (!d.conditions.length) {
            throw TR("推理规则不包含假设，无法与条件匹配");
        }
        if (idx === "mp")
            throw TR("元推理结论 >mp 为 (($0 > $1) ⊢ ($0 > $1))，假设与结论相同");
        // ...A, B |- C
        const offsetTable = [];
        const offsetCondTable = [];
        let s; // condAst
        const steps = this.getProofSteps(d);
        const dependsOnDischarged = d.conditions.map((_, i) => i === d.conditions.length - 1);
        for (const [i, step] of steps.entries()) {
            this.evaluation.check();
            const current = d.conditions.length + i;
            dependsOnDischarged[current] = step.conditionIdxs.some(id => dependsOnDischarged[id >= 0 ? id : current + id]);
        }
        const generate = (condMode, idx) => {
            this.evaluation.enter();
            try {
                return generateChecked(condMode, idx);
            }
            finally {
                this.evaluation.leave();
            }
        };
        const generateChecked = (condMode, idx) => {
            idx ??= steps.length - 1 + d.conditions.length;
            const step = steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                if (dependsOnDischarged[idx])
                    return -1;
                // avoid repeated deductions on the same prop
                if (isFinite(offsetTable[idx]))
                    return offsetTable[idx];
                // here if reaching hyp B, roll back
                if (!step) {
                    return -1;
                }
                // Dependency analysis above avoids speculative deductions and
                // quadratic snapshots of the growing proposition list.
                const condIdxs = [];
                for (const id of step.conditionIdxs) {
                    const n = generate(false, id >= 0 ? id : idx + id);
                    condIdxs.push(n);
                }
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: step.replaceValues,
                    conditionIdxs: condIdxs
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx]))
                return offsetCondTable[idx];
            // B: B>B
            if (idx === d.conditions.length - 1) {
                return offsetCondTable[idx] = this.deduct({ deductionIdx: ".i", conditionIdxs: [], replaceValues: [s] });
            }
            const p0 = generate(false, idx);
            // if deduction steps don't contain hyp B
            if (p0 !== -1) {
                return offsetCondTable[idx] = this.deduct({
                    deductionIdx: "<a1", conditionIdxs: [p0],
                    replaceValues: [s]
                });
            }
            this.metaConditionTheorem(sdidx, "中间步骤");
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: "c" + sdidx, replaceValues: step.replaceValues,
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        };
        const oldP = this.propositions;
        try {
            this.fastmetarules += "<";
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                if (id !== d.conditions.length - 1) {
                    this.addHypothese(c);
                    offsetTable.push(id);
                }
                else {
                    s = c;
                }
            });
            generate(true);
            const ret = this.addMacro(">" + idx, from);
            this.propositions = oldP;
            this.fastmetarules = fastrule;
            return ret;
        }
        catch (e) {
            this.fastmetarules = fastrule;
            this.propositions = oldP;
            throw e;
        }
    }
    metaInvDeductTheorem(idx, from) {
        return this.generateRule(() => this.metaInvDeductTheoremChecked(idx, from));
    }
    metaInvDeductTheoremChecked(idx, from) {
        // >a => a
        if (idx[0] === ">") {
            this.generateDeduction(idx.slice(1));
            return idx.slice(1);
        }
        // a => <a
        if (this.deductions["<" + idx])
            return "<" + idx;
        const d = this.generateDeduction(idx);
        const oldP = this.propositions;
        const conclusion = d.conclusion;
        if (conclusion.type !== "sym" || conclusion.name !== ">")
            throw TR("条件推理规则(...$$0 ⊢ ($$1 > $$2))匹配失败");
        const [ss1, ss2] = conclusion.nodes;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => this.addHypothese(c));
            const nhyp = this.addHypothese(ss1);
            const ss1_ss2 = this.deduct({
                deductionIdx: idx, conditionIdxs: d.conditions.map((v, id) => id),
                replaceValues: d.replaceNames.map(str => ({ type: "replvar", name: str }))
            });
            this.deduct({ deductionIdx: "mp", replaceValues: [], conditionIdxs: [ss1_ss2, nhyp] });
            const ret = this.addMacro("<" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaCompleteTheorem(ast, name, from) {
        return this.evaluate(() => this.metaCompleteTheoremChecked(ast, name, from));
    }
    metaCompleteTheoremChecked(ast, name, from) {
        const proof = new Proof(this);
        const p = this.propositions;
        try {
            this.propositions = [];
            proof.prove(ast);
            this.addMacro(name, from);
            this.propositions = p;
        }
        catch (e) {
            this.propositions = p;
            throw e;
        }
        return name;
    }
    metaCombineTheorem(idx1s, idx2, from) {
        return this.generateRule(() => this.metaCombineTheoremChecked(idx1s, idx2, from));
    }
    metaCombineTheoremChecked(idx1s, idx2, from) {
        const name = ":" + idx1s.join(":") + "," + idx2;
        if (this.deductions[name])
            return name;
        const d2 = this.generateDeduction(idx2);
        if (d2.conditions.length < idx1s.length)
            throw TR("匹配条件推理规则($$1b, ...$$2 ⊢ $$3)失败");
        while (d2.conditions.length > idx1s.length)
            idx1s.push("#");
        const d1s = idx1s.map(e => e === "#" ? null : this.generateDeduction(e));
        const oldP = this.propositions;
        const cloneAndRename = (ast, postfix) => {
            const R = astmgr.clone(ast);
            const rename = (a) => {
                if (a.type === "replvar" && a.name.startsWith("$")) {
                    a.name = a.name + postfix;
                }
                if (a.nodes?.length) {
                    for (const n of a.nodes) {
                        rename(n);
                    }
                }
            };
            return rename(R), R;
        };
        // rename replvars in d1s and d2
        const d1conds = d1s.map((d, i) => {
            if (!d)
                return null;
            return d.conditions.map(c => cloneAndRename(c, String(i + 1)));
        });
        const d1concs = d1s.map((d, i) => {
            if (!d)
                return null;
            return cloneAndRename(d.conclusion, "" + String(i + 1));
        });
        const d2cond = d2.conditions.map(e => cloneAndRename(e, "0"));
        const d1replaceNames = d1s.map((d, i) => d ? d.replaceNames.map(dr => ({ type: "replvar", name: dr + String(i + 1) })) : []);
        const d2replaceNames = d2.replaceNames.map(dr => ({ type: "replvar", name: dr + "0" }));
        // generate and solve constrains
        const constrains = [];
        for (let i = 0; i < d1s.length; i++) {
            if (!d1concs[i])
                continue;
            constrains.push([d1concs[i], d2cond[i], false]);
        }
        const solver = new ConstrainSolver();
        const assertions = [];
        const mt = solver.solveConstrain(constrains, assertions);
        // solver.dbg(mt, constrains, assertions);
        const nfTable = solver.addAssertions(mt, assertions);
        // use match table to replace all iteratively (include itself, nftable and dconds/dconcs)
        const finished = new Set;
        for (const key in mt) {
            const v = mt[key];
            const k = { type: "replvar", name: key };
            finished.add(key);
            const RP = (ast) => {
                astmgr.replace(ast, k, v);
            };
            for (const key2 in mt) {
                if (finished.has(key2))
                    continue;
                RP(mt[key2]);
            }
            for (const key2 in nfTable) {
                RP(nfTable[key2][0]);
            }
            d1conds.forEach(conds => {
                if (!conds)
                    return;
                conds.forEach(c => RP(c));
            });
            d2cond.forEach(c => RP(c));
            d1replaceNames.forEach(c => c.forEach(sc => RP(sc)));
            d2replaceNames.forEach(c => RP(c));
        }
        // add nf fn from match table
        for (const key2 in nfTable) {
            const k = { type: "replvar", name: key2 };
            const RP = (ast) => {
                astmgr.replace(ast, k, nfTable[key2][0]);
            };
            d1conds.forEach(conds => {
                if (!conds)
                    return;
                conds.forEach(c => RP(c));
            });
            d2cond.forEach(c => RP(c));
            d1replaceNames.forEach(c => c.forEach(sc => RP(sc)));
            d2replaceNames.forEach(c => RP(c));
        }
        try {
            this.removePropositions();
            const hyps = d1conds.map((c, idx) => c ? c.map(c => this.addHypothese(c)) : [this.addHypothese(d2cond[idx])]);
            const pcs = [];
            for (let i = 0; i < d1conds.length; i++) {
                if (idx1s[i] === "#")
                    pcs.push(hyps[i][0]);
                else
                    pcs.push(this.deduct({
                        deductionIdx: idx1s[i], conditionIdxs: hyps[i],
                        replaceValues: d1replaceNames[i]
                    }));
            }
            this.deduct({
                deductionIdx: idx2, conditionIdxs: pcs,
                replaceValues: d2replaceNames
            });
            const ret = this.addMacro(name, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaIffTheorem(idx, replaceValues, name, from, allowIFFT_RP) {
        return this.evaluate(() => this.metaIffTheoremChecked(idx, replaceValues, name, from, allowIFFT_RP));
    }
    metaIffTheoremChecked(idx, replaceValues, name, from, allowIFFT_RP) {
        const d = this.generateDeduction(idx);
        if (!d)
            throw TR("推理规则不存在");
        if (d.conditions?.length)
            throw TR("条件推理规则( ⊢ ($$0 <> $$1))匹配失败");
        const conclusion = d.conclusion;
        if (conclusion.type !== "sym" || conclusion.name !== "<>")
            throw TR("条件推理规则( ⊢ ($$0 <> $$1))匹配失败");
        const [A, B] = conclusion.nodes;
        const [C, N] = replaceValues;
        if (N.type !== "replvar")
            throw TR("匹配序号参数必须为非负整数");
        let nth = Number(N.name);
        if (!isFinite(nth) || Math.floor(nth) !== nth || nth < 0)
            throw TR("匹配序号参数必须为非负整数");
        nth -= 1;
        const oldP = this.propositions;
        const R = astmgr.clone(C);
        assert.matchSubAndReplace(R, A, B, nth, /^\$/, false, 0, assert.getReplVarsType(R, {}, false));
        let A_B;
        let replacedNth = 0;
        // generate a <> b or VxVyVz a<>b
        const generate = (a, b, Vs = []) => {
            const prefix = "".padEnd(Vs.length, "v");
            if (astmgr.equal(a, b)) {
                // example: (~~a>~~b) <> (~~a > b), also count ~~a one time
                try {
                    const matched = {};
                    assert.match(a, A, /^\$/, false, matched, {}, null, []);
                    replacedNth++;
                }
                catch (e) { }
                // a == b : a <> a
                return this.deduct({ deductionIdx: prefix + ".<>i", conditionIdxs: [], replaceValues: [...Vs, a] });
            }
            try {
                const matched = {};
                assert.match(a, A, /^\$/, false, matched, {}, null, []);
                replacedNth++;
                if (nth === -1 || nth + 1 === replacedNth) {
                    return this.deduct({
                        deductionIdx: prefix + idx, conditionIdxs: [],
                        replaceValues: [...Vs, ...d.replaceNames.map(str => matched[str])]
                    });
                }
            }
            catch (e) { }
            if (!a.nodes?.length || a.nodes?.length !== b.nodes?.length) {
                throw TR("元推理函数中替换函数##rp执行失败");
            }
            if (a.type !== b.type || a.name !== b.name) {
                throw TR("元推理函数中替换函数##rp执行失败");
            }
            if (a.type === "sym") {
                if (a.name === ">" || a.name === "<>" || a.name === "&" || a.name === "|") {
                    return this.deduct({
                        deductionIdx: prefix + ".<>r" + a.name, replaceValues: [],
                        conditionIdxs: [generate(a.nodes[0], b.nodes[0], Vs), generate(a.nodes[1], b.nodes[1], Vs)],
                    });
                }
                if (a.name === "~") {
                    return this.deduct({
                        deductionIdx: prefix + ".<>rn", replaceValues: [],
                        conditionIdxs: [generate(a.nodes[0], b.nodes[0], Vs)],
                    });
                }
                if (a.name === "V") {
                    const vab = generate(a.nodes[1], b.nodes[1], [...Vs, a.nodes[0]]);
                    return this.deduct({
                        deductionIdx: prefix + ".<>rV", replaceValues: [],
                        conditionIdxs: [vab],
                    });
                }
                if (a.name === "E") {
                    const vab = generate(a.nodes[1], b.nodes[1], [...Vs, a.nodes[0]]);
                    return this.deduct({
                        deductionIdx: prefix + ".<>rE", replaceValues: [],
                        conditionIdxs: [vab],
                    });
                }
                if (a.name === "E!") {
                    if (!allowIFFT_RP) {
                        throw TR("还未解锁跨越量词E!进行替换的功能");
                    }
                    const vab = generate(a.nodes[1], b.nodes[1], [...Vs, a.nodes[0]]);
                    return this.deduct({
                        deductionIdx: prefix + ".<>rE!", replaceValues: [],
                        conditionIdxs: [vab],
                    });
                }
            }
        };
        try {
            this.removePropositions();
            generate(C, R);
            const ret = this.addMacro(name, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
}
//# sourceMappingURL=formalsystem.js.map