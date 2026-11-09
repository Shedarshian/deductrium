import { AST, ASTMgr } from "./astmgr.js";
import { ASTParser } from "./astparser.js";
import type { FormalSystem } from "./formalsystem.js";
import type { Deduction } from "./formalsystem.js";
export type InductionRecipe = { template: AST; targetName: string; rules: string[] };

const mgr = new ASTMgr();
const parser = new ASTParser();
export const modelSyntaxOptions = {
    unfoldAnd: true, unfoldOr: true, unfoldIff: true, unfoldExists: true,
};
export type ModelKind = "sat" | "abs" | "all";
export const isModelOperation = (a: AST) => a?.type === "fn" &&
    ["#sat", "#abs", "#abst", "#absf"].includes(a.name);
export const containsModelOperation = (a: AST): boolean => isModelOperation(a) ||
    !!a?.nodes?.some(containsModelOperation);
export const containsArgumentList = (a: AST): boolean => a?.type === "arglist" || !!a?.nodes?.some(containsArgumentList);
export function templateNames(a: AST, names = new Map<string, "predicate" | "list">()) {
    if (a.type === "predtemplate" || a.type === "predref") names.set(a.name, "predicate");
    if (a.type === "arglist") names.set(a.name, "list");
    a.nodes?.forEach(n => templateNames(n, names));
    return names;
}
const v = (name: string): AST => ({ type: "replvar", name });
const sym = (name: string, ...nodes: AST[]): AST => ({ type: "sym", name, nodes });
const fn = (name: string, ...nodes: AST[]): AST => ({ type: "fn", name, nodes });
const sat = (a: AST, d: AST) => fn("#sat", mgr.clone(a), mgr.clone(d));
const all = (xs: AST[], body: AST) => xs.reduce((r, x) => sym("V", mgr.clone(x), r), body);

type Definition = { name: string; kind: "predicate" | "function" | "constant";
    parameters: AST[]; body: AST; output?: AST; rule: string };

/** No model registry: definitions and interpretation recipes live in ordinary rules. */
export class ModelOperations {
    constructor(private fs: FormalSystem) { }

    private fail(message: string): never { throw new Error(message); }

    private plainVariable(a: AST): boolean {
        return a?.type === "replvar" && !a.name.startsWith("$") &&
            !a.name.startsWith("#") && !this.fs.assert.isConst(a.name) &&
            /^[a-z_][a-z0-9_]*$/.test(a.name);
    }

    private stripUniversals(a: AST): { params: AST[]; body: AST } {
        const params: AST[] = [];
        while (a.type === "sym" && a.name === "V" && a.nodes?.length === 2) {
            if (!this.plainVariable(a.nodes[0])) this.fail("定义参数必须是明确的普通变量");
            params.push(a.nodes[0]); a = a.nodes[1];
        }
        if (new Set(params.map(p => p.name)).size !== params.length) this.fail("定义参数不能重复");
        return { params, body: a };
    }

    private substitute(a: AST, replacements: Map<string, AST>): AST {
        const present = mgr.getVarNames(a, new Set<string>(), null);
        if (![...replacements.keys()].some(name => present.has(name))) return mgr.clone(a);
        if (a.type === "replvar") return mgr.clone(replacements.get(a.name) ?? a);
        if (isModelOperation(a)) {
            const domain = mgr.clone(a.nodes[1]);
            if (domain.type === "fn" || domain.type === "predtemplate") {
                domain.nodes = [domain.nodes[0], ...domain.nodes.slice(1).map(p => this.substitute(p, replacements))];
            }
            return fn(a.name, this.substitute(a.nodes[0], replacements), domain);
        }
        if (a.type === "sym" && ["V", "E", "E!", "{|", "|}"].includes(a.name)) {
            const bound = a.nodes[0];
            if (!this.plainVariable(bound)) this.fail("暂不支持带断言的绑定变量");
            const inner = new Map(replacements); inner.delete(bound.name);
            const bodyIndex = a.name === "{|" || a.name === "|}" ? 2 : 1;
            const bodyNames = mgr.getVarNames(a.nodes[bodyIndex], new Set<string>(), null);
            for (const key of inner.keys()) if (!bodyNames.has(key)) inner.delete(key);
            for (const r of inner.values()) {
                if (containsArgumentList(r)) this.fail("未绑定参数列表的自由变量不确定，不能穿过绑定变量替换");
                const free = new Set<string>(); this.fs.assert.getFreeVars(r, free);
                if (free.has(bound.name)) this.fail("替换可能捕获变量；请先展开并换名");
            }
            return { ...a, nodes: a.nodes.map((n, i) => i === 0 ? mgr.clone(n) : this.substitute(n, i === bodyIndex ? inner : replacements)) };
        }
        return { ...a, nodes: a.nodes?.map(n => this.substitute(n, replacements)) };
    }

    inspectDefinition(rule: string): Definition {
        const d = this.fs.deductions[rule];
        if (!d || d.conditions.length || d.steps?.length || !d.from.endsWith("*")) {
            return this.fail("需要由定义元规则引入的无前提 df/dv/dc 定义");
        }
        const name = rule.slice(2);
        const stripped = this.stripUniversals(d.conclusion);
        const c = stripped.body;
        let result: Definition;
        if (rule.startsWith("dv") && this.fs.verbs.has(name) && c.name === "<>" && c.type === "sym" &&
            c.nodes?.length === 2 && c.nodes[0].type === "fn" && c.nodes[0].name === name) {
            const parameters = c.nodes[0].nodes;
            if (!parameters.length || parameters.some(p => !this.plainVariable(p)) ||
                new Set(parameters.map(p => p.name)).size !== parameters.length ||
                stripped.params.length !== parameters.length ||
                stripped.params.some(p => !parameters.some(x => mgr.equal(p, x)))) this.fail("无法核验谓词定义的参数");
            result = { rule, name, kind: "predicate", parameters, body: c.nodes[1] };
        } else if ((rule.startsWith("df") || rule.startsWith("dc")) && !stripped.params.length &&
            c.type === "sym" && c.name === ">" && c.nodes?.length === 2) {
            const left = this.stripUniversals(c.nodes[0]);
            const right = this.stripUniversals(c.nodes[1]);
            const e = left.body;
            if (e.type !== "sym" || e.name !== "E" || !this.plainVariable(e.nodes?.[0]) ||
                !mgr.equal(fn("params", ...left.params), fn("params", ...right.params))) this.fail("无法核验选择定义的存在前提");
            // mf wraps its parameter quantifiers in reverse argument order.
            const parameters = left.params.slice().reverse();
            const constant = rule.startsWith("dc");
            if (constant ? parameters.length !== 0 || !this.fs.consts.has(name) :
                parameters.length === 0 || !this.fs.fns.has(name)) this.fail("定义符号类别不符");
            if (parameters.some(p => p.name === e.nodes[0].name)) this.fail("输出变量与输入参数冲突");
            const value = constant ? v(name) : fn(name, ...parameters);
            const replaced = this.substitute(e.nodes[1], new Map([[e.nodes[0].name, value]]));
            if (!mgr.equal(replaced, right.body)) this.fail("定义的结论与存在前提不匹配");
            result = { rule, name, kind: constant ? "constant" : "function", parameters,
                body: e.nodes[1], output: e.nodes[0] };
        } else return this.fail("暂不支持此定义模式，不能只根据名称前缀相对化");
        const free = new Set<string>(); this.fs.assert.getFreeVars(result.body, free);
        const allowed = new Set([...result.parameters.map(p => p.name), result.output?.name]);
        if ([...free].some(x => !this.fs.assert.isConst(x) && !allowed.has(x))) this.fail("定义体存在未声明的自由参数");
        const cyclic = (a: AST): boolean => a.name === name || !!a.nodes?.some(cyclic);
        if (cyclic(result.body)) this.fail("不能解释自引用定义");
        return result;
    }

    checkDomain(domain: AST): void {
        if (domain.type === "predref") {
            if (domain.nodes?.length) this.fail("裸论域模板不能携带参数");
            this.checkTemplateName(domain.name); return;
        }
        if (domain.type === "predtemplate" || domain.type === "fn") {
            const slot = domain.nodes?.[0];
            if (slot?.type !== "replvar" || slot.name !== "_" || slot.nodes?.length) this.fail("参数化论域的第一个参数必须是唯一的 _ 元素槽");
            const containsSlot = (a: AST): boolean => a.type === "replvar" && a.name === "_" || !!a.nodes?.some(containsSlot);
            const types = {};
            for (const [i, a] of this.domainArguments(domain).entries()) {
                if (containsSlot(a)) this.fail("论域只能含一个 _ 元素槽，且必须在首位");
                if (a.type === "arglist") {
                    if (domain.type !== "predtemplate" || i !== domain.nodes.length - 2 || a.nodes?.length || !/^\.\.\.\$[a-z_][a-z0-9_]*$/.test(a.name)) this.fail("论域尾列表只能用于谓词模板的末尾");
                } else { this.fs.assert.checkGrammer(a, "i"); this.fs.assert.getReplVarsType(a, types, true); }
            }
            if (domain.type === "predtemplate") { this.checkTemplateName(domain.name); return; }
            const d = this.inspectDefinition("dv" + domain.name);
            if (d.kind !== "predicate" || d.parameters.length !== domain.nodes.length) this.fail("参数化论域的实际元数与 mprd 定义不符");
            return;
        }
        if (domain.type !== "replvar" || domain.name.startsWith('"')) this.fail("论域必须是 mprd 谓词引用，或 p(_,a,b) 形式的局部模板");
        const definition = this.inspectDefinition("dv" + domain.name);
        if (definition.kind !== "predicate" || definition.parameters.length !== 1) this.fail("论域谓词必须是一元");
    }
    domainArguments(domain: AST): AST[] {
        return domain.type === "fn" || domain.type === "predtemplate" ? domain.nodes.slice(1) : [];
    }

    checkTemplateName(name: string) {
        if (!/^"[a-z_][a-z0-9_]*$/.test(name)) this.fail("谓词模板名称无效");
        if (this.fs.consts.has(name) || this.fs.fns.has(name) || this.fs.verbs.has(name)) this.fail("此双引号名称已有旧符号定义，不能同时用作谓词模板");
    }

    predicateBinding(value: AST): AST {
        if (value.type === "predref") {
            if (value.nodes?.length) this.fail("裸谓词引用不能携带参数");
            this.checkTemplateName(value.name);
            return { type: "predicatebinding", name: value.name, nodes: [v("-1")] };
        }
        if (value.type !== "replvar") this.fail("谓词参数需要一个已由 mprd 定义的具体谓词名");
        const d = this.inspectDefinition("dv" + value.name);
        return { type: "predicatebinding", name: d.name, nodes: [v(String(d.parameters.length))] };
    }

    argumentBinding(value: AST): AST {
        if (value.type === "arglist" && !value.nodes?.length && /^\.\.\.\$[a-z_][a-z0-9_]*$/.test(value.name)) return { type: "argbinding", name: "", nodes: [mgr.clone(value)] };
        if (value.type !== "fn" || !["#args", "("].includes(value.name)) this.fail("参数列表请输入 #args(t1,t2,...)；空列表为 #args()");
        const types = {};
        for (const [i, term] of value.nodes.entries()) {
            if (term.type === "arglist" && !term.nodes?.length && i === value.nodes.length - 1 && /^\.\.\.\$[a-z_][a-z0-9_]*$/.test(term.name)) continue;
            if (containsArgumentList(term)) this.fail("参数列表只能在末尾保留一个抽象列表");
            this.fs.assert.checkGrammer(term, "i"); this.fs.assert.getReplVarsType(term, types, true);
        }
        return { type: "argbinding", name: "", nodes: value.nodes.map(t => mgr.clone(t)) };
    }
    private bindingInput(value: AST): AST {
        if (value.type === "predicatebinding") return { type: value.name.startsWith('"') ? "predref" : "replvar", name: value.name };
        if (value.type === "argbinding") return fn("#args", ...value.nodes.map(t => mgr.clone(t)));
        return mgr.clone(value);
    }

    private guard(domain: AST, term: AST): AST {
        return { type: domain.type === "predref" || domain.type === "predtemplate" ? "predtemplate" : "fn", name: domain.name,
            nodes: [mgr.clone(term), ...this.domainArguments(domain).map(a => mgr.clone(a))] };
    }

    private alias(source: string, domain: AST): string {
        let hash = 2166136261;
        const count = this.domainArguments(domain).length;
        const key = source + ":" + domain.name + (count ? "/" + count : "");
        for (let i = 0; i < key.length; i++) hash = Math.imul(hash ^ key.charCodeAt(i), 16777619) >>> 0;
        return "model" + hash.toString(36);
    }

    private form(d: Definition, domain: AST) {
        if (!["replvar", "fn"].includes(domain.type) || containsArgumentList(domain)) this.fail("内部定义需要已绑定的具体论域和固定参数列表");
        const used = mgr.getVarNames(d.body, new Set<string>(), null);
        d.parameters.forEach(p => used.add(p.name));
        if (d.output) used.add(d.output.name);
        const extra: AST[] = [];
        let next = 0;
        const actual = this.domainArguments(domain);
        for (const _ of actual) {
            let name: string;
            do { name = "modelparam" + next++; } while (used.has(name) || this.fs.assert.isConst(name));
            used.add(name); extra.push(v(name));
        }
        return { extra, actual, parameters: [...extra, ...d.parameters],
            domain: extra.length ? fn(domain.name, v("_"), ...extra.map(p => mgr.clone(p))) : v(domain.name) };
    }

    private definitionName(d: Definition, domain: AST, alias: string) {
        return (d.kind === "predicate" ? "dv" : d.kind === "constant" && !this.domainArguments(domain).length ? "dc" : "df") + alias;
    }

    private recipe(d: Definition, domain: AST) {
        return "模型解释:" + encodeURIComponent(JSON.stringify([d.rule, parser.stringifyTight(this.form(d, domain).domain)])) + "*";
    }

    private relativeBody(d: Definition, domain: AST): AST {
        // Interpret the open body BEFORE substituting the chosen internal value.
        // Leaving #sat(R(z),D) opaque here would make mc/mf reinterpret that value.
        let body = this.meaning(sat(d.body, domain), false, { left: 4096 });
        if (d.kind !== "predicate") {
            body = sym("&", this.guard(domain, d.output), body);
            if (d.parameters.length) {
                const guards = d.parameters.map(p => this.guard(domain, p));
                body = sym(">", guards.reduce((a, b) => sym("&", a, b)), body);
            }
        }
        return body;
    }

    private relativeDefinition(d: Definition, domain: AST, name: string): AST {
        const form = this.form(d, domain);
        const body = this.relativeBody(d, form.domain);
        if (d.kind === "predicate") return all(form.parameters, sym("<>", fn(name, ...form.parameters.map(p => mgr.clone(p))), body));
        const value = form.parameters.length ? fn(name, ...form.parameters.map(p => mgr.clone(p))) : v(name);
        const applied = this.substitute(body, new Map([[d.output.name, value]]));
        return sym(">", all(form.parameters, sym("E", mgr.clone(d.output), body)), all(form.parameters, applied));
    }

    private interpretation(d: Definition, domain: AST): string {
        this.form(d, domain);
        const alias = this.alias(d.rule, domain);
        const rule = this.definitionName(d, domain, alias);
        const existing = this.fs.deductions[rule];
        if (!existing || existing.from !== this.recipe(d, domain) || existing.steps?.length || existing.conditions.length ||
            !mgr.equal(existing.conclusion, this.relativeDefinition(d, domain, alias))) {
            this.fail("缺少经过核验的内部解释，请先对 " + d.rule + " 使用 sat-def");
        }
        return alias;
    }

    define(source: string, domain: AST): string {
        this.checkDomain(domain);
        const d = this.inspectDefinition(source);
        const form = this.form(d, domain);
        const alias = this.alias(source, domain);
        const name = this.definitionName(d, domain, alias);
        if (this.fs.deductions[name]) { this.interpretation(d, domain); return name; }
        // An apparently unused name may already occur as an unregistered symbol.
        const occurs = (a: AST): boolean => a.name === alias || !!a.nodes?.some(occurs);
        if (this.fs.consts.has(alias) || this.fs.fns.has(alias) || this.fs.verbs.has(alias) ||
            Object.values(this.fs.deductions).some(x => occurs(x.value)) || this.fs.propositions.some(x => occurs(x.value))) {
            this.fail("内部解释名称冲突，拒绝覆盖已有符号");
        }
        const body = this.relativeBody(d, form.domain);
        const from = this.recipe(d, domain);
        // Reuse the existing conservative definition mechanism, retaining its existence premise.
        let created: string;
        try {
            if (d.kind === "predicate") created = this.fs.metaNewVerb([v(alias), body, form.parameters], from);
            else if (!form.parameters.length) created = this.fs.metaNewConstant([v(alias), d.output, body], from);
            else created = this.fs.metaNewFunction([v(alias), d.output, body, form.parameters], from);
            this.interpretation(d, domain);
            return created;
        } catch (e) {
            if (created) delete this.fs.deductions[created];
            this.fs.consts.delete(alias); this.fs.fns.delete(alias); this.fs.verbs.delete(alias);
            throw e;
        }
    }

    nodes(source: AST, kind: ModelKind = "all"): { path: number[]; node: AST }[] {
        const result: { path: number[]; node: AST }[] = [];
        const visit = (a: AST, path: number[]) => {
            if (isModelOperation(a) && (kind === "all" || (a.name === "#sat" ? "sat" : "abs") === kind)) result.push({ path, node: a });
            a.nodes?.forEach((n, i) => { if (!isModelOperation(a) || i === 0) visit(n, [...path, i]); });
        };
        visit(source, []); return result;
    }

    private term(a: AST, domain: AST): AST {
        if (this.plainVariable(a)) return mgr.clone(a);
        return sat(a, domain);
    }

    private objectFreeVars(a: AST, result = new Set<string>(), scope = new Set<string>(), item = false): Set<string> {
        if (a.type === "arglist") this.fail("对象自由变量依赖尚未绑定的参数列表");
        if (a.type === "replvar") {
            if (item && !scope.has(a.name) && !this.fs.assert.isConst(a.name)) result.add(a.name);
            return result;
        }
        if (isModelOperation(a)) return this.objectFreeVars(a.nodes[0], result, scope, this.fs.assert.getSubAstType(a, 0, item));
        const q = this.fs.assert.getQuantParams(a);
        if (q) {
            const name = this.fs.assert.getVarName(q[0]);
            if (!name) this.fail("自由变量分析需要可核验的绑定变量");
            return this.objectFreeVars(q[1], result, new Set([...scope, name]), false);
        }
        if (a.type === "sym" && ["{|", "|}"].includes(a.name)) {
            const name = this.fs.assert.getVarName(a.nodes[0]);
            if (!name) this.fail("自由变量分析需要可核验的集合绑定变量");
            this.objectFreeVars(a.nodes[1], result, scope, true);
            return this.objectFreeVars(a.nodes[2], result, new Set([...scope, name]), a.name === "|}");
        }
        a.nodes?.forEach((n, i) => this.objectFreeVars(n, result, scope, this.fs.assert.getSubAstType(a, i, item)));
        return result;
    }

    private quantify(body: AST, domain: AST): AST {
        let bound = mgr.clone(body.nodes[0]);
        let inner = mgr.clone(body.nodes[1]);
        const params = this.domainArguments(domain);
        const absence = params.map(p => this.fs.assert.nf(bound.name, p));
        if (absence.includes(0)) this.fail("域固定参数的自由变量尚未确定，无法核验量词展开");
        if (absence.includes(-1)) {
            const schematic = (a: AST): boolean => a.type === "arglist" || a.type === "replvar" && a.name.startsWith("$") || !!a.nodes?.some(schematic);
            if (schematic(inner) || params.some(schematic)) this.fail("量词需要卫生换名，请先实例化涉及的公式或项模板");
            const names = mgr.getVarNames(body, new Set<string>(), null);
            mgr.getVarNames(domain, names, null);
            let index = 0, name: string;
            do { name = "modelq" + index++; } while (names.has(name) || this.fs.assert.isConst(name));
            inner = this.substitute(inner, new Map([[bound.name, v(name)]]));
            bound = v(name);
        }
        return sym(body.name, bound, sym(body.name === "V" ? ">" : "&", this.guard(domain, bound), sat(inner, domain)));
    }

    /** Only documented defining conversions, never arbitrary externally proved equivalences. */
    private one(a: AST, isItem: boolean, semantic: boolean, budget: { left: number }): AST {
        if (--budget.left < 0) this.fail("展开预算超限，未生成新定理");
        if (!isModelOperation(a) || a.nodes?.length !== 2) return this.fail("目标不是合法的模型操作");
        const [body, domain] = a.nodes;
        this.checkDomain(domain);
        if (a.name !== "#sat") {
            if (a.name === "#abs") this.fail("请用 #abst 或 #absf 明确绝对性的类别");
            if (a.name === "#abst") return sym("&", this.guard(domain, body), sym("=", sat(body, domain), mgr.clone(body)));
            // Schematic formula variables have unknown free variables: no guessed guard list.
            const reject = (n: AST) => {
                if (isModelOperation(n)) { reject(n.nodes[0]); return; }
                if (n.type === "arglist") this.fail("参数列表的自由变量尚未确定，不能展开绝对性");
                if (n.type === "replvar" && n.name.startsWith("$")) this.fail("公式模板的自由变量尚未确定，不能展开绝对性");
                if (n.type === "fn" && n.name.startsWith("#") && !isModelOperation(n)) this.fail("请先处理公式内的系统断言");
                n.nodes?.forEach(reject);
            };
            reject(body);
            const guards = [...this.objectFreeVars(body)].sort().map(x => this.guard(domain, v(x)));
            const iff = sym("<>", mgr.clone(body), sat(body, domain));
            return guards.length ? sym(">", guards.reduce((x, y) => sym("&", x, y)), iff) : iff;
        }
        if (isModelOperation(body)) {
            return sat(this.meaning(body, isItem, budget), domain);
        }
        if (isItem) {
            if (this.plainVariable(body)) return mgr.clone(body);
            const source = body.type === "replvar" && this.fs.assert.isConst(body.name) ? "dc" + body.name :
                body.type === "fn" && this.fs.fns.has(body.name) ? "df" + body.name : "";
            if (!source) this.fail("该内部项尚无支持的定义解释；替换变量不能假定为普通变量");
            const d = this.inspectDefinition(source);
            const alias = this.interpretation(d, domain);
            const params = this.domainArguments(domain).map(p => mgr.clone(p));
            if (d.kind === "constant") return params.length ? fn(alias, ...params) : v(alias);
            if (body.nodes?.length !== d.parameters.length) this.fail("函数实参数量不符");
            return fn(alias, ...params, ...body.nodes.map(t => this.term(t, domain)));
        }
        if (body.type === "sym" && ["@", "="].includes(body.name) && body.nodes?.length === 2) {
            return sym(body.name, ...body.nodes.map(t => this.term(t, domain)));
        }
        if (body.type === "sym" && body.name === "~" && body.nodes?.length === 1) return sym("~", sat(body.nodes[0], domain));
        if (body.type === "sym" && [">", "&", "|", "<>"].includes(body.name) && body.nodes?.length === 2) {
            const option = { "&": "unfoldAnd", "|": "unfoldOr", "<>": "unfoldIff" }[body.name];
            if (!semantic && option && !modelSyntaxOptions[option]) this.fail("此连接词的直接展开已关闭");
            return sym(body.name, ...body.nodes.map(n => sat(n, domain)));
        }
        if (body.type === "sym" && ["V", "E"].includes(body.name) && body.nodes?.length === 2) {
            if (!this.plainVariable(body.nodes[0]) && !(body.nodes[0].type === "replvar" && /^\$[a-zA-Z0-9_]+$/.test(body.nodes[0].name))) this.fail("量词展开需要普通变量或位于绑定位置的变量模板");
            if (!semantic && body.name === "E" && !modelSyntaxOptions.unfoldExists) this.fail("存在量词的直接展开已关闭");
            return this.quantify(body, domain);
        }
        if (body.type === "fn" && this.fs.verbs.has(body.name)) {
            const d = this.inspectDefinition("dv" + body.name);
            if (d.parameters.length !== body.nodes?.length) this.fail("谓词实参数量不符");
            return fn(this.interpretation(d, domain), ...this.domainArguments(domain).map(p => mgr.clone(p)), ...body.nodes.map(t => this.term(t, domain)));
        }
        if (body.type === "predtemplate") this.fail("请先把谓词模板及参数列表绑定为具体的 mprd 谓词");
        return this.fail("此公式结构尚无可靠的相对化展开规则");
    }

    private meaning(a: AST, isItem: boolean, budget: { left: number }): AST {
        if (--budget.left < 0) this.fail("嵌套解释预算超限");
        if (isModelOperation(a)) return this.meaning(this.one(a, isItem, true, budget), isItem, budget);
        return { ...a, nodes: a.nodes?.map((n, i) => this.meaning(n, this.fs.assert.getSubAstType(a, i, isItem), budget)) };
    }

    unfold(source: AST, path: number[], expected: AST, replay = false): AST {
        const result = mgr.clone(source);
        let node = result, item = false, underModel = false;
        for (const i of path) {
            if (!Number.isInteger(i) || i < 0 || !node.nodes?.[i] || (isModelOperation(node) && i !== 0)) this.fail("展开目标路径无效");
            underModel ||= isModelOperation(node);
            item = this.fs.assert.getSubAstType(node, i, item); node = node.nodes[i];
        }
        if (!isModelOperation(node) || !mgr.equal(node, expected)) this.fail("展开目标已变化，拒绝按旧编号替换");
        const replacement = this.one(node, item, replay, { left: 4096 });
        mgr.assign(node, replacement);
        this.fs.assert.checkGrammer(result, "p"); this.fs.assert.getReplVarsType(result, {}, false);
        if (underModel && !mgr.equal(this.meaning(source, false, { left: 4096 }), this.meaning(result, false, { left: 4096 }))) {
            this.fail("无法核验外层模型上下文中的定义转换");
        }
        return result;
    }

    private property(template: AST, formula: AST): AST {
        return this.substitute(template, new Map([["#slot", formula]]));
    }

    private applyBranch(rule: string, goal: AST, available: number[], budget: { left: number }): number {
        this.fs.assert.checkGrammer(goal, "p");
        const d = this.fs.generateDeduction(rule);
        if (!d) this.fail("结构归纳分支规则不存在：" + rule);
        const initial: { [key: string]: AST } = {};
        const types: { [key: string]: boolean } = {};
        this.fs.assert.match(goal, d.conclusion, /^\$/, false, initial, types, null, []);
        const search = (n: number, table: { [key: string]: AST }, selected: number[]): number => {
            if (--budget.left < 0) this.fail("归纳分支匹配预算超限");
            if (n === d.conditions.length) {
                if (d.replaceNames.some(x => !table[x])) this.fail("分支仍有无法确定的参数");
                const index = this.fs.deduct({ deductionIdx: rule, conditionIdxs: selected,
                    replaceValues: d.replaceNames.map(x => this.bindingInput(table[x])) });
                if (!mgr.equal(this.fs.propositions[index].value, goal)) this.fail("归纳分支实际结论与目标不符");
                return index;
            }
            let last: unknown;
            for (const index of available) {
                const copy = Object.fromEntries(Object.entries(table).map(([k, a]) => [k, mgr.clone(a)]));
                try { this.fs.assert.match(this.fs.propositions[index].value, d.conditions[n], /^\$/, false, copy, { ...types }, null, []); }
                catch { continue; }
                const before = this.fs.propositions.slice();
                try { return search(n + 1, copy, [...selected, index]); }
                catch (e) { this.fs.propositions = before; last = e; if (budget.left < 0) throw e; }
            }
            this.fail("分支前提或侧条件不能由子式结果和指定共同前提满足" + (last ? "：" + last : ""));
        };
        return search(0, initial, []);
    }

    private checkProperty(template: AST, generic: boolean) {
        const types = this.fs.assert.getReplVarsType(template, {}, false);
        if (types["#slot"] !== false) this.fail("性质模板必须在公式位置包含 #slot");
        const walk = (a: AST, bound: boolean) => {
            if (a.type === "replvar" && a.name.startsWith("#") && a.name !== "#slot") this.fail("性质模板不能含证明局部变量");
            if (generic && a.type === "replvar" && a.name === "#slot" && bound) this.fail("通用归纳的公式槽不能位于对象量词的作用域内");
            if (generic && a.type === "fn" && a.name.startsWith("#") && !isModelOperation(a)) this.fail("通用性质模板不能将系统断言当成公式槽的性质");
            a.nodes?.forEach((n, i) => walk(n, bound || a.type === "sym" && ["V", "E", "E!", "{|", "|}"].includes(a.name) && i === (a.name === "{|" || a.name === "|}" ? 2 : 1)));
        };
        walk(template, false);
    }

    /** Verify schematic branches with fresh rigid metavariables, not sampled formulas. */
    validateInduction(recipe: InductionRecipe, common: AST[]): { quantified: boolean; existentialQuantified: boolean } {
        if (!recipe || !/^\$[a-zA-Z0-9_]+$/.test(recipe.targetName) || !Array.isArray(recipe.rules) || ![5, 9].includes(recipe.rules.length) || recipe.rules.some(r => typeof r !== "string" || !r)) this.fail("结构归纳规则的配方无效");
        if (!Array.isArray(common) || common.length > 1024) this.fail("归纳共同前提数量超限");
        this.checkProperty(recipe.template, true);
        const names = mgr.getVarNames(recipe.template, new Set<string>(), null);
        for (const c of common) {
            this.fs.assert.checkGrammer(c, "p");
            mgr.getVarNames(c, names, null);
            const local = (a: AST): boolean => a.type === "replvar" && a.name.startsWith("#") || !!a.nodes?.some(local);
            if (local(c)) this.fail("共同前提不能依赖证明局部变量或 #slot");
        }
        if (names.has(recipe.targetName)) this.fail("目标公式参数不能已在性质模板或共同前提中出现");
        const visited = new Set<Deduction>();
        let dependencyBudget = 4096;
        const inspect = (d: Deduction) => {
            if (!d) this.fail("归纳分支缺少依赖规则");
            if (visited.has(d)) return;
            if (--dependencyBudget < 0) this.fail("分支依赖分析预算超限");
            visited.add(d);
            if (d.induction) this.fail("归纳分支暂不能依赖另一条结构归纳生成规则");
            mgr.getVarNames(d.value, names, null);
            d.steps?.forEach(step => {
                step.replaceValues.forEach(a => mgr.getVarNames(a, names, null));
                if (step.model) mgr.getVarNames(step.model.target, names, null);
                if (step.generalize) mgr.getVarNames(step.generalize, names, null);
                inspect(this.fs.generateDeduction(step.deductionIdx));
            });
        };
        recipe.rules.forEach(r => inspect(this.fs.generateDeduction(r)));
        let serial = 0;
        const fresh = () => { let name: string; do { name = "$mi_probe_" + serial++; } while (names.has(name)); names.add(name); return v(name); };
        const [a, b, x, y] = [fresh(), fresh(), fresh(), fresh()];
        const cases = [sym("@", x, y), sym("=", x, y), sym("~", a), sym(">", a, b), sym("V", x, a),
            sym("&", a, b), sym("|", a, b), sym("<>", a, b), sym("E", x, a)];
        const children: AST[][] = [[], [], [a], [a, b], [a], [a, b], [a, b], [a, b], [a]];
        const old = this.fs.propositions;
        const budget = { left: 16384 };
        let quantified = false, existentialQuantified = false;
        try {
            for (let i = 0; i < recipe.rules.length; i++) {
                const run = (quantifiedIH: boolean) => {
                    this.fs.propositions = [];
                    const available = common.map(c => this.fs.addHypothese(c, true));
                    children[i].forEach(child => {
                        const ih = this.property(recipe.template, child);
                        available.push(this.fs.addHypothese(quantifiedIH ? sym("V", mgr.clone(x), ih) : ih, true));
                    });
                    this.applyBranch(recipe.rules[i], this.property(recipe.template, cases[i]), available, budget);
                };
                try { run(false); }
                catch (directError) {
                    if ((i !== 4 && i !== 8) || budget.left < 0) throw new Error("第 " + (i + 1) + " 个通用分支未通过核验：" + directError);
                    try { run(true); if (i === 4) quantified = true; else existentialQuantified = true; }
                    catch (quantifiedError) { throw new Error((i === 4 ? "全称" : "存在") + "分支既不能由 T[A]，也不能由 Vx:T[A] 推出目标：" + quantifiedError); }
                }
            }
            return { quantified, existentialQuantified };
        } finally { this.fs.propositions = old; }
    }

    createInduction(name: string, template: AST, targetName: string, rules: string[], common: AST[]): string {
        if (!/^[a-z_][a-z0-9_]*$/.test(name) || /^[acdempuv]/.test(name) || this.fs.deductions[name]) this.fail("归纳规则需要一个未占用的普通自定义规则名");
        const recipe: InductionRecipe = { template: mgr.clone(template), targetName, rules: rules.slice() };
        this.validateInduction(recipe, common);
        const value: AST = { type: "meta", name: "⊢", nodes: [fn("#array", ...common.map(c => mgr.clone(c))), fn("#array", this.property(recipe.template, v(targetName)))] };
        this.fs.addDeduction(name, value, "结构归纳规则（纯关系语言，逐实例核验量词侧条件）*");
        this.fs.deductions[name].induction = recipe;
        return name;
    }

    validateInductionDefinition(d: Deduction): { quantified: boolean; existentialQuantified: boolean } {
        if (!d.induction || d.steps?.length || d.tempvars?.size) this.fail("结构归纳规则不能同时带普通宏步骤或局部变量");
        const result = this.validateInduction(d.induction, d.conditions);
        const goal = this.property(d.induction.template, v(d.induction.targetName));
        this.fs.assert.checkGrammer(goal, "p");
        if (!mgr.equal(goal, d.conclusion)) this.fail("归纳配方与所声明的规则结论不一致");
        return result;
    }

    /** Elaborate each concrete instance into checked existing inference steps. */
    induct(template: AST, target: AST, rules: string[], common: number[], quantified?: boolean, existentialQuantified?: boolean): number {
        if (![5, 9].includes(rules.length)) this.fail("需要五个基础分支；扩展模式还须提供合取、析取、互推、存在四个分支");
        if (common.some(i => !Number.isInteger(i) || i < 0 || !this.fs.propositions[i])) this.fail("共同前提定理编号无效");
        this.checkProperty(template, false);
        const before = this.fs.propositions.slice();
        const budget = { left: 4096 };
        const construct = (a: AST): number => {
            if (--budget.left < 0) this.fail("结构递归预算超限");
            let branch: number; let children: AST[] = [];
            if (a.type === "sym" && ["@", "="].includes(a.name) && a.nodes?.length === 2 && a.nodes.every(x => this.plainVariable(x))) branch = a.name === "@" ? 0 : 1;
            else if (a.type === "sym" && a.name === "~" && a.nodes?.length === 1) { branch = 2; children = a.nodes; }
            else if (a.type === "sym" && a.name === ">" && a.nodes?.length === 2) { branch = 3; children = a.nodes; }
            else if (a.type === "sym" && a.name === "V" && a.nodes?.length === 2 && this.plainVariable(a.nodes[0])) { branch = 4; children = [a.nodes[1]]; }
            else if (rules.length === 9 && a.type === "sym" && ["&", "|", "<>"].includes(a.name) && a.nodes?.length === 2) {
                branch = { "&": 5, "|": 6, "<>": 7 }[a.name]; children = a.nodes;
            } else if (rules.length === 9 && a.type === "sym" && a.name === "E" && a.nodes?.length === 2 && this.plainVariable(a.nodes[0])) { branch = 8; children = [a.nodes[1]]; }
            else return this.fail("目标超出所选归纳范围；扩展模式需要额外的 &、|、<>、E 分支，函数项和额外谓词仍须先可靠消去");
            const results = children.map(construct);
            const quantifier = branch === 4 || branch === 8;
            const mode = branch === 4 ? quantified : branch === 8 ? existentialQuantified : false;
            const attempt = (quantifiedIH: boolean) => {
                const snapshot = this.fs.propositions.slice();
                try {
                    const ih = results.map(index => quantifiedIH ? this.fs.generalizeModel(index, a.nodes[0]) : index);
                    return this.applyBranch(rules[branch], this.property(template, a), [...common, ...ih], budget);
                } catch (e) { this.fs.propositions = snapshot; throw e; }
            };
            if (!quantifier || mode !== undefined) return attempt(!!mode);
            try { return attempt(false); }
            catch (directError) {
                if (budget.left < 0) throw directError;
                return attempt(true);
            }
        };
        try { return construct(target); }
        catch (e) { this.fs.propositions = before; throw e; }
    }
}
