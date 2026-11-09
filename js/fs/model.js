import { ASTMgr } from "./astmgr.js";
import { ASTParser } from "./astparser.js";
const mgr = new ASTMgr();
const parser = new ASTParser();
export const modelSyntaxOptions = {
    unfoldAnd: true, unfoldOr: true, unfoldIff: true, unfoldExists: true,
};
export const isModelOperation = (a) => a?.type === "fn" &&
    ["#sat", "#abs", "#abst", "#absf"].includes(a.name);
export const containsModelOperation = (a) => isModelOperation(a) ||
    !!a?.nodes?.some(containsModelOperation);
export const containsArgumentList = (a) => a?.type === "arglist" || !!a?.nodes?.some(containsArgumentList);
export function templateNames(a, names = new Map()) {
    if (a.type === "predtemplate" || a.type === "predref")
        names.set(a.name, "predicate");
    if (a.type === "arglist")
        names.set(a.name, "list");
    a.nodes?.forEach(n => templateNames(n, names));
    return names;
}
const v = (name) => ({ type: "replvar", name });
const sym = (name, ...nodes) => ({ type: "sym", name, nodes });
const fn = (name, ...nodes) => ({ type: "fn", name, nodes });
const sat = (a, d) => fn("#sat", mgr.clone(a), mgr.clone(d));
const all = (xs, body) => xs.reduce((r, x) => sym("V", mgr.clone(x), r), body);
/** No model registry: definitions and interpretation recipes live in ordinary rules. */
export class ModelOperations {
    fs;
    constructor(fs) {
        this.fs = fs;
    }
    fail(message) { throw new Error(message); }
    plainVariable(a) {
        return a?.type === "replvar" && !a.name.startsWith("$") &&
            !a.name.startsWith("#") && !this.fs.assert.isConst(a.name) &&
            /^[a-z_][a-z0-9_]*$/.test(a.name);
    }
    stripUniversals(a) {
        const params = [];
        while (a.type === "sym" && a.name === "V" && a.nodes?.length === 2) {
            if (!this.plainVariable(a.nodes[0]))
                this.fail("定义参数必须是明确的普通变量");
            params.push(a.nodes[0]);
            a = a.nodes[1];
        }
        if (new Set(params.map(p => p.name)).size !== params.length)
            this.fail("定义参数不能重复");
        return { params, body: a };
    }
    substitute(a, replacements) {
        if (a.type === "replvar")
            return mgr.clone(replacements.get(a.name) ?? a);
        if (a.type === "sym" && ["V", "E", "E!", "{|", "|}"].includes(a.name)) {
            const bound = a.nodes[0];
            if (!this.plainVariable(bound))
                this.fail("暂不支持带断言的绑定变量");
            const inner = new Map(replacements);
            inner.delete(bound.name);
            for (const r of inner.values()) {
                if (containsArgumentList(r))
                    this.fail("未绑定参数列表的自由变量不确定，不能穿过绑定变量替换");
                const free = new Set();
                this.fs.assert.getFreeVars(r, free);
                if (free.has(bound.name))
                    this.fail("替换可能捕获变量；请先展开并换名");
            }
            return { ...a, nodes: a.nodes.map((n, i) => i === 0 ? mgr.clone(n) : this.substitute(n, inner)) };
        }
        return { ...a, nodes: a.nodes?.map(n => this.substitute(n, replacements)) };
    }
    inspectDefinition(rule) {
        const d = this.fs.deductions[rule];
        if (!d || d.conditions.length || d.steps?.length || !d.from.endsWith("*")) {
            return this.fail("需要由定义元规则引入的无前提 df/dv/dc 定义");
        }
        const name = rule.slice(2);
        const stripped = this.stripUniversals(d.conclusion);
        const c = stripped.body;
        let result;
        if (rule.startsWith("dv") && this.fs.verbs.has(name) && c.name === "<>" && c.type === "sym" &&
            c.nodes?.length === 2 && c.nodes[0].type === "fn" && c.nodes[0].name === name) {
            const parameters = c.nodes[0].nodes;
            if (!parameters.length || parameters.some(p => !this.plainVariable(p)) ||
                new Set(parameters.map(p => p.name)).size !== parameters.length ||
                stripped.params.length !== parameters.length ||
                stripped.params.some(p => !parameters.some(x => mgr.equal(p, x))))
                this.fail("无法核验谓词定义的参数");
            result = { rule, name, kind: "predicate", parameters, body: c.nodes[1] };
        }
        else if ((rule.startsWith("df") || rule.startsWith("dc")) && !stripped.params.length &&
            c.type === "sym" && c.name === ">" && c.nodes?.length === 2) {
            const left = this.stripUniversals(c.nodes[0]);
            const right = this.stripUniversals(c.nodes[1]);
            const e = left.body;
            if (e.type !== "sym" || e.name !== "E" || !this.plainVariable(e.nodes?.[0]) ||
                !mgr.equal(fn("params", ...left.params), fn("params", ...right.params)))
                this.fail("无法核验选择定义的存在前提");
            // mf wraps its parameter quantifiers in reverse argument order.
            const parameters = left.params.slice().reverse();
            const constant = rule.startsWith("dc");
            if (constant ? parameters.length !== 0 || !this.fs.consts.has(name) :
                parameters.length === 0 || !this.fs.fns.has(name))
                this.fail("定义符号类别不符");
            if (parameters.some(p => p.name === e.nodes[0].name))
                this.fail("输出变量与输入参数冲突");
            const value = constant ? v(name) : fn(name, ...parameters);
            const replaced = this.substitute(e.nodes[1], new Map([[e.nodes[0].name, value]]));
            if (!mgr.equal(replaced, right.body))
                this.fail("定义的结论与存在前提不匹配");
            result = { rule, name, kind: constant ? "constant" : "function", parameters,
                body: e.nodes[1], output: e.nodes[0] };
        }
        else
            return this.fail("暂不支持此定义模式，不能只根据名称前缀相对化");
        const free = new Set();
        this.fs.assert.getFreeVars(result.body, free);
        const allowed = new Set([...result.parameters.map(p => p.name), result.output?.name]);
        if ([...free].some(x => !this.fs.assert.isConst(x) && !allowed.has(x)))
            this.fail("定义体存在未声明的自由参数");
        const cyclic = (a) => a.name === name || !!a.nodes?.some(cyclic);
        if (cyclic(result.body))
            this.fail("不能解释自引用定义");
        return result;
    }
    checkDomain(domain) {
        if (domain.type === "predref") {
            if (domain.nodes?.length)
                this.fail("裸论域模板不能携带参数");
            this.checkTemplateName(domain.name);
            return;
        }
        if (domain.type !== "replvar" || domain.name.startsWith('"')) {
            this.fail("本阶段的论域必须是已用 mprd 定义的一元谓词名；模板和固定参数域尚未开放");
        }
        const definition = this.inspectDefinition("dv" + domain.name);
        if (definition.kind !== "predicate" || definition.parameters.length !== 1)
            this.fail("论域谓词必须是一元");
    }
    checkTemplateName(name) {
        if (!/^"[a-z_][a-z0-9_]*$/.test(name))
            this.fail("谓词模板名称无效");
        if (this.fs.consts.has(name) || this.fs.fns.has(name) || this.fs.verbs.has(name))
            this.fail("此双引号名称已有旧符号定义，不能同时用作谓词模板");
    }
    predicateBinding(value) {
        if (value.type !== "replvar")
            this.fail("谓词参数需要一个已由 mprd 定义的具体谓词名");
        const d = this.inspectDefinition("dv" + value.name);
        return { type: "predicatebinding", name: d.name, nodes: [v(String(d.parameters.length))] };
    }
    argumentBinding(value) {
        if (value.type !== "fn" || !["#args", "("].includes(value.name))
            this.fail("参数列表请输入 #args(t1,t2,...)；空列表为 #args()");
        const types = {};
        for (const term of value.nodes) {
            if (containsArgumentList(term))
                this.fail("具体参数列表不能再包含未绑定列表");
            this.fs.assert.checkGrammer(term, "i");
            this.fs.assert.getReplVarsType(term, types, true);
        }
        return { type: "argbinding", name: "", nodes: value.nodes.map(t => mgr.clone(t)) };
    }
    bindingInput(value) {
        if (value.type === "predicatebinding")
            return v(value.name);
        if (value.type === "argbinding")
            return fn("#args", ...value.nodes.map(t => mgr.clone(t)));
        return mgr.clone(value);
    }
    guard(domain, term) {
        return { type: domain.type === "predref" ? "predtemplate" : "fn", name: domain.name, nodes: [mgr.clone(term)] };
    }
    alias(source, domain) {
        let hash = 2166136261;
        const key = source + ":" + parser.stringifyTight(domain);
        for (let i = 0; i < key.length; i++)
            hash = Math.imul(hash ^ key.charCodeAt(i), 16777619) >>> 0;
        return "model" + hash.toString(36);
    }
    recipe(source, domain) {
        return "模型解释:" + encodeURIComponent(JSON.stringify([source, parser.stringifyTight(domain)])) + "*";
    }
    relativeBody(d, domain) {
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
    relativeDefinition(d, domain, name) {
        const body = this.relativeBody(d, domain);
        if (d.kind === "predicate")
            return all(d.parameters, sym("<>", fn(name, ...d.parameters.map(p => mgr.clone(p))), body));
        const value = d.kind === "constant" ? v(name) : fn(name, ...d.parameters.map(p => mgr.clone(p)));
        const applied = this.substitute(body, new Map([[d.output.name, value]]));
        return sym(">", all(d.parameters, sym("E", mgr.clone(d.output), body)), all(d.parameters, applied));
    }
    interpretation(d, domain) {
        if (domain.type !== "replvar")
            this.fail("需要先将论域模板绑定到具体的一元 mprd 谓词");
        const alias = this.alias(d.rule, domain);
        const rule = (d.kind === "predicate" ? "dv" : d.kind === "constant" ? "dc" : "df") + alias;
        const existing = this.fs.deductions[rule];
        if (!existing || existing.from !== this.recipe(d.rule, domain) || existing.steps?.length || existing.conditions.length ||
            !mgr.equal(existing.conclusion, this.relativeDefinition(d, domain, alias))) {
            this.fail("缺少经过核验的内部解释，请先对 " + d.rule + " 使用 sat-def");
        }
        return alias;
    }
    define(source, domain) {
        this.checkDomain(domain);
        if (domain.type !== "replvar")
            this.fail("sat-def 需要具体的一元论域谓词，不能为未绑定模板创建定义");
        const d = this.inspectDefinition(source);
        const alias = this.alias(source, domain);
        const name = (d.kind === "predicate" ? "dv" : d.kind === "constant" ? "dc" : "df") + alias;
        if (this.fs.deductions[name]) {
            this.interpretation(d, domain);
            return name;
        }
        // An apparently unused name may already occur as an unregistered symbol.
        const occurs = (a) => a.name === alias || !!a.nodes?.some(occurs);
        if (this.fs.consts.has(alias) || this.fs.fns.has(alias) || this.fs.verbs.has(alias) ||
            Object.values(this.fs.deductions).some(x => occurs(x.value)) || this.fs.propositions.some(x => occurs(x.value))) {
            this.fail("内部解释名称冲突，拒绝覆盖已有符号");
        }
        const body = this.relativeBody(d, domain);
        const from = this.recipe(source, domain);
        // Reuse the existing conservative definition mechanism, retaining its existence premise.
        let created;
        try {
            if (d.kind === "predicate")
                created = this.fs.metaNewVerb([v(alias), body, d.parameters], from);
            else if (d.kind === "constant")
                created = this.fs.metaNewConstant([v(alias), d.output, body], from);
            else
                created = this.fs.metaNewFunction([v(alias), d.output, body, d.parameters], from);
            this.interpretation(d, domain);
            return created;
        }
        catch (e) {
            if (created)
                delete this.fs.deductions[created];
            this.fs.consts.delete(alias);
            this.fs.fns.delete(alias);
            this.fs.verbs.delete(alias);
            throw e;
        }
    }
    nodes(source, kind = "all") {
        const result = [];
        const visit = (a, path) => {
            if (isModelOperation(a) && (kind === "all" || (a.name === "#sat" ? "sat" : "abs") === kind))
                result.push({ path, node: a });
            a.nodes?.forEach((n, i) => { if (!isModelOperation(a) || i === 0)
                visit(n, [...path, i]); });
        };
        visit(source, []);
        return result;
    }
    term(a, domain) {
        if (this.plainVariable(a))
            return mgr.clone(a);
        return sat(a, domain);
    }
    /** Only documented defining conversions, never arbitrary externally proved equivalences. */
    one(a, isItem, semantic, budget) {
        if (--budget.left < 0)
            this.fail("展开预算超限，未生成新定理");
        if (!isModelOperation(a) || a.nodes?.length !== 2)
            return this.fail("目标不是合法的模型操作");
        const [body, domain] = a.nodes;
        this.checkDomain(domain);
        if (a.name !== "#sat") {
            if (a.name === "#abs")
                this.fail("请用 #abst 或 #absf 明确绝对性的类别");
            if (a.name === "#abst")
                return sym("&", this.guard(domain, body), sym("=", sat(body, domain), mgr.clone(body)));
            // Schematic formula variables have unknown free variables: no guessed guard list.
            const reject = (n) => {
                if (n.type === "arglist")
                    this.fail("参数列表的自由变量尚未确定，不能展开绝对性");
                if (n.type === "replvar" && n.name.startsWith("$"))
                    this.fail("公式模板的自由变量尚未确定，不能展开绝对性");
                if (n.type === "fn" && n.name.startsWith("#") && !isModelOperation(n))
                    this.fail("请先处理公式内的系统断言");
                n.nodes?.forEach(reject);
            };
            reject(body);
            const free = new Set();
            this.fs.assert.getFreeVars(body, free);
            const guards = [...free].filter(x => !this.fs.assert.isConst(x)).sort().map(x => this.guard(domain, v(x)));
            const iff = sym("<>", mgr.clone(body), sat(body, domain));
            return guards.length ? sym(">", guards.reduce((x, y) => sym("&", x, y)), iff) : iff;
        }
        if (isModelOperation(body)) {
            return sat(this.meaning(body, isItem, budget), domain);
        }
        if (isItem) {
            if (this.plainVariable(body))
                return mgr.clone(body);
            const source = body.type === "replvar" && this.fs.assert.isConst(body.name) ? "dc" + body.name :
                body.type === "fn" && this.fs.fns.has(body.name) ? "df" + body.name : "";
            if (!source)
                this.fail("该内部项尚无支持的定义解释；替换变量不能假定为普通变量");
            const d = this.inspectDefinition(source);
            const alias = this.interpretation(d, domain);
            if (d.kind === "constant")
                return v(alias);
            if (body.nodes?.length !== d.parameters.length)
                this.fail("函数实参数量不符");
            return fn(alias, ...body.nodes.map(t => this.term(t, domain)));
        }
        if (body.type === "sym" && ["@", "="].includes(body.name) && body.nodes?.length === 2) {
            return sym(body.name, ...body.nodes.map(t => this.term(t, domain)));
        }
        if (body.type === "sym" && body.name === "~" && body.nodes?.length === 1)
            return sym("~", sat(body.nodes[0], domain));
        if (body.type === "sym" && [">", "&", "|", "<>"].includes(body.name) && body.nodes?.length === 2) {
            const option = { "&": "unfoldAnd", "|": "unfoldOr", "<>": "unfoldIff" }[body.name];
            if (!semantic && option && !modelSyntaxOptions[option])
                this.fail("此连接词的直接展开已关闭");
            return sym(body.name, ...body.nodes.map(n => sat(n, domain)));
        }
        if (body.type === "sym" && ["V", "E"].includes(body.name) && body.nodes?.length === 2) {
            if (!this.plainVariable(body.nodes[0]))
                this.fail("量词展开需要确定的普通绑定变量");
            if (!semantic && body.name === "E" && !modelSyntaxOptions.unfoldExists)
                this.fail("存在量词的直接展开已关闭");
            return sym(body.name, mgr.clone(body.nodes[0]), sym(body.name === "V" ? ">" : "&", this.guard(domain, body.nodes[0]), sat(body.nodes[1], domain)));
        }
        if (body.type === "fn" && this.fs.verbs.has(body.name)) {
            const d = this.inspectDefinition("dv" + body.name);
            if (d.parameters.length !== body.nodes?.length)
                this.fail("谓词实参数量不符");
            return fn(this.interpretation(d, domain), ...body.nodes.map(t => this.term(t, domain)));
        }
        if (body.type === "predtemplate")
            this.fail("请先把谓词模板及参数列表绑定为具体的 mprd 谓词");
        return this.fail("此公式结构尚无可靠的相对化展开规则");
    }
    meaning(a, isItem, budget) {
        if (--budget.left < 0)
            this.fail("嵌套解释预算超限");
        if (isModelOperation(a))
            return this.meaning(this.one(a, isItem, true, budget), isItem, budget);
        return { ...a, nodes: a.nodes?.map((n, i) => this.meaning(n, this.fs.assert.getSubAstType(a, i, isItem), budget)) };
    }
    unfold(source, path, expected, replay = false) {
        const result = mgr.clone(source);
        let node = result, item = false, underModel = false;
        for (const i of path) {
            if (!Number.isInteger(i) || i < 0 || !node.nodes?.[i] || (isModelOperation(node) && i !== 0))
                this.fail("展开目标路径无效");
            underModel ||= isModelOperation(node);
            item = this.fs.assert.getSubAstType(node, i, item);
            node = node.nodes[i];
        }
        if (!isModelOperation(node) || !mgr.equal(node, expected))
            this.fail("展开目标已变化，拒绝按旧编号替换");
        const replacement = this.one(node, item, replay, { left: 4096 });
        mgr.assign(node, replacement);
        this.fs.assert.checkGrammer(result, "p");
        this.fs.assert.getReplVarsType(result, {}, false);
        if (underModel && !mgr.equal(this.meaning(source, false, { left: 4096 }), this.meaning(result, false, { left: 4096 }))) {
            this.fail("无法核验外层模型上下文中的定义转换");
        }
        return result;
    }
    /** Finite proof construction; it does NOT assert an unproved schema for all formulas. */
    induct(template, target, rules, common) {
        if (rules.length !== 5)
            this.fail("依次提供属于、相等、否定、蕴含、全称五个分支规则");
        if (common.some(i => !Number.isInteger(i) || i < 0 || !this.fs.propositions[i]))
            this.fail("共同前提定理编号无效");
        const types = this.fs.assert.getReplVarsType(template, {}, false);
        if (types["#slot"] !== false)
            this.fail("性质模板必须在公式位置包含 #slot");
        const before = this.fs.propositions.slice();
        let budget = 4096;
        const property = (a) => this.substitute(template, new Map([["#slot", a]]));
        const construct = (a) => {
            if (--budget < 0)
                this.fail("结构递归预算超限");
            let branch;
            let children = [];
            if (a.type === "sym" && ["@", "="].includes(a.name) && a.nodes?.length === 2 && a.nodes.every(x => this.plainVariable(x)))
                branch = a.name === "@" ? 0 : 1;
            else if (a.type === "sym" && a.name === "~" && a.nodes?.length === 1) {
                branch = 2;
                children = a.nodes;
            }
            else if (a.type === "sym" && a.name === ">" && a.nodes?.length === 2) {
                branch = 3;
                children = a.nodes;
            }
            else if (a.type === "sym" && a.name === "V" && a.nodes?.length === 2 && this.plainVariable(a.nodes[0])) {
                branch = 4;
                children = [a.nodes[1]];
            }
            else
                return this.fail("归纳范围仅覆盖变量原子 x@y、x=y 及 ~、>、V；其余符号须先可靠消去");
            const available = [...common, ...children.map(construct)];
            const goal = property(a);
            this.fs.assert.checkGrammer(goal, "p");
            const d = this.fs.generateDeduction(rules[branch]);
            const initial = {};
            const varTypes = {};
            this.fs.assert.match(goal, d.conclusion, /^\$/, false, initial, varTypes, null, []);
            const search = (n, table, selected) => {
                if (--budget < 0)
                    this.fail("分支匹配预算超限");
                if (n === d.conditions.length) {
                    if (d.replaceNames.some(x => !table[x]))
                        this.fail("分支仍有无法确定的参数");
                    const index = this.fs.deduct({ deductionIdx: rules[branch], conditionIdxs: selected,
                        replaceValues: d.replaceNames.map(x => this.bindingInput(table[x])) });
                    if (!mgr.equal(this.fs.propositions[index].value, goal))
                        this.fail("归纳分支实际结论与目标不符");
                    return index;
                }
                for (const index of available) {
                    const copy = Object.fromEntries(Object.entries(table).map(([k, a]) => [k, mgr.clone(a)]));
                    try {
                        this.fs.assert.match(this.fs.propositions[index].value, d.conditions[n], /^\$/, false, copy, { ...varTypes }, null, []);
                    }
                    catch {
                        continue;
                    }
                    const length = this.fs.propositions.length;
                    try {
                        return search(n + 1, copy, [...selected, index]);
                    }
                    catch (e) {
                        this.fs.propositions.splice(length);
                        if (budget < 0)
                            throw e;
                    }
                }
                return this.fail("分支规则的前提无法由子式结果和指定的共同前提满足");
            };
            return search(0, initial, []);
        };
        try {
            return construct(target);
        }
        catch (e) {
            this.fs.propositions = before;
            throw e;
        }
    }
}
//# sourceMappingURL=model.js.map