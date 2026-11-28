import { ASTMgr } from "./astmgr.js";
const mgr = new ASTMgr;
const rightConjunction = "::<a1,:.&m2:>.&1,c.&,c.&s";
const leftConjunction = "::<a1,.cs,:.&m2:>.&2,c.&";
const atom = (name) => ({ type: "replvar", name });
const is = (ast, name) => ast.type === "sym" && ast.name === name;
function planInstantiation(fs, formula) {
    let nodes = 0;
    const noQuantifiers = (ast, depth = 0) => {
        if (++nodes > 100_000 || depth > 128)
            throw new Error("公式过大或嵌套过深 / Formula too large or deeply nested");
        if (ast.name.includes("$"))
            throw new Error("所选公式不能含有 $ / The selected formula must not contain $");
        let quantifierFree = !["V", "E", "E!"].some(q => is(ast, q));
        for (const child of ast.nodes ?? [])
            quantifierFree = noQuantifiers(child, depth + 1) && quantifierFree;
        return quantifierFree;
    };
    noQuantifiers(formula);
    const quantifierFree = (ast) => !["V", "E", "E!"].some(q => is(ast, q)) &&
        (ast.nodes ?? []).every(quantifierFree);
    const binders = [];
    const binderAt = new Map();
    const addBinder = (ast, path) => {
        const name = fs.assert.getVarName(ast.nodes[0]);
        if (!name)
            throw new Error("量词的约束变量无效 / Invalid bound variable");
        const binder = { path, kind: ast.name, original: name, local: name, parameter: "", excludes: new Set };
        binders.push(binder);
        binderAt.set(ast, binder);
    };
    const tail = (ast, path) => {
        if (is(ast, "E")) {
            addBinder(ast, path);
            tail(ast.nodes[1], [...path, 1]);
        }
        else if (is(ast, "&"))
            ast.nodes.forEach((child, i) => tail(child, [...path, i]));
        else if (!quantifierFree(ast))
            throw new Error("存在量词只能嵌套在存在量词或合取中 / Existentials must be nested only in existentials or conjunctions");
    };
    const prefix = (ast, path) => {
        if (is(ast, "V")) {
            addBinder(ast, path);
            return prefix(ast.nodes[1], [...path, 1]);
        }
        if (is(ast, ">") && quantifierFree(ast.nodes[0]))
            return prefix(ast.nodes[1], [...path, 1]);
        tail(ast, path);
        return path;
    };
    const suffix = prefix(formula, []);
    // Track binding occurrences, not just spellings: Vx:...Ex:... and two
    // independent Ex branches must not accidentally share renaming constraints.
    const occurrences = (ast, scope, existentials) => {
        const binder = binderAt.get(ast);
        if (binder) {
            const inner = new Map(scope);
            inner.set(binder.original, binder);
            occurrences(ast.nodes[1], inner, binder.kind === "E" ? [...existentials, binder] : existentials);
            return;
        }
        const nf = fs.assert.getNfParams(ast);
        if (nf) {
            occurrences(nf[0], scope, existentials);
            return;
        }
        if (ast.type === "replvar") {
            const owner = scope.get(ast.name);
            if (owner)
                for (const e of existentials)
                    if (binders.indexOf(owner) < binders.indexOf(e))
                        owner.excludes.add(e);
            return;
        }
        if (is(ast, "{|") || is(ast, "|}")) {
            occurrences(ast.nodes[1], scope, existentials);
            const inner = new Map(scope);
            inner.delete(fs.assert.getVarName(ast.nodes[0]));
            occurrences(ast.nodes[2], inner, existentials);
            return;
        }
        for (const child of ast.nodes ?? [])
            occurrences(child, scope, existentials);
    };
    occurrences(formula, new Map, []);
    const reserved = mgr.getVarNames(formula, new Set, null);
    for (const p of fs.propositions)
        mgr.getVarNames(p.value, reserved, null);
    for (const name of fs.consts)
        reserved.add(name);
    const localNames = new Set(), parameterNames = new Set();
    const fresh = (base, used) => {
        let name = base, i = 0;
        while (used.has(name))
            name = base + (++i);
        used.add(name);
        return name;
    };
    for (const [i, b] of binders.entries()) {
        const base = b.original.replace(/^#+/, "") || "x";
        b.parameter = fresh("$" + base, parameterNames);
        if ((i === 0 && b.kind === "V") || (b.original.startsWith("#") && !localNames.has(b.original)))
            b.local = b.original;
        else
            b.local = fresh("#" + base, reserved);
        localNames.add(b.local);
    }
    return { binders, suffix };
}
function liftAt(formula, path, rule) {
    if (!path.length)
        return rule;
    const [side, ...rest] = path;
    const inner = liftAt(formula.nodes[side], rest, rule);
    if (is(formula, "V") && side === 1)
        return "v" + inner;
    if (is(formula, "E") && side === 1)
        return "e" + inner;
    if (is(formula, ">") && side === 1)
        return "c" + inner;
    if (is(formula, "&"))
        return "<:>" + inner + "," + (side === 0 ? leftConjunction : rightConjunction);
    throw new Error("不支持此处的量词结构 / Unsupported quantifier context");
}
/** Append ordinary, kernel-checked proof steps. No theorem values or proof
 * certificates are fabricated. A private working proposition list makes
 * hypothesis insertion/reindexing atomic, even when a later check fails. */
export async function instantiateQuantifiers(fs, index, options = {}) {
    const selected = fs.propositions[index];
    if (!selected)
        throw new Error("请选择定理栏中的完整定理 / Select a complete proposition");
    const plan = planInstantiation(fs, selected.value);
    const original = fs.propositions;
    const working = original.map(p => ({ value: p.value, from: p.from ?
            { ...p.from, conditionIdxs: [...p.from.conditionIdxs], replaceValues: [...p.from.replaceValues] } : null }));
    fs.propositions = working;
    let current = working[index], steps = 0, assumptions = 0, expectedLength = working.length;
    let expectedOrder = working.slice();
    const check = () => {
        if (options.signal?.aborted)
            throw new Error("操作已取消 / Operation cancelled");
        if ((options.isCurrent && !options.isCurrent()) || fs.propositions !== working || working.length !== expectedLength ||
            working.some((p, i) => p !== expectedOrder[i]))
            throw new Error("操作状态已变化，请重试 / Operation state changed");
    };
    const deduct = async (name, values, premises = [current]) => {
        check();
        await fs.prepareExpansion(name, { signal: options.signal });
        check();
        const result = fs.deduct({ deductionIdx: name, conditionIdxs: premises.map(p => working.indexOf(p)), replaceValues: values });
        current = working[result];
        expectedLength = working.length;
        expectedOrder = working.slice();
        steps++;
        options.onProgress?.(steps);
        check();
    };
    const valueFor = (b) => {
        const names = [...b.excludes].map(e => e.parameter);
        return names.length ? { type: "fn", name: "#nf", nodes: [atom(b.parameter), ...names.map(atom)] } : atom(b.parameter);
    };
    try {
        check();
        // Inner-to-outer alpha conversion prevents a later binder from capturing
        // an occurrence while outer quantifiers and antecedents are still there.
        for (const b of [...plan.binders].reverse()) {
            if (b.local === b.original)
                continue;
            await deduct(liftAt(current.value, b.path, b.kind === "V" ? ".Vcn" : ".Ecn"), [atom(b.local)]);
        }
        const universals = plan.binders.filter(b => b.kind === "V");
        let universal = 0;
        while (is(current.value, "V") || is(current.value, ">")) {
            if (is(current.value, "V"))
                await deduct("<a4", [valueFor(universals[universal++])]);
            else {
                check();
                const implication = current;
                fs.addHypothese(mgr.clone(current.value.nodes[0]));
                expectedLength = working.length;
                expectedOrder = working.slice();
                const hypothesis = working.filter(p => !p.from).at(-1);
                assumptions++;
                await deduct("mp", [], [implication, hypothesis]);
            }
        }
        // Outer-to-inner E conversion lets each earlier parameter carry just
        // the nf guards needed by the later existential scopes that use it.
        for (const b of plan.binders.filter(b => b.kind === "E"))
            await deduct(liftAt(current.value, b.path.slice(plan.suffix.length), ".Ecn"), [valueFor(b)]);
        check();
        return { index: working.indexOf(current), steps, assumptions };
    }
    catch (error) {
        if (fs.propositions === working)
            fs.propositions = original;
        throw error;
    }
}
//# sourceMappingURL=instantiate.js.map