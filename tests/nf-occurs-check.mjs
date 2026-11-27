import assert from 'node:assert/strict';
import test from 'node:test';
import { AssertionSystem } from '../js/fs/assertion.js';
import { ASTMgr } from '../js/fs/astmgr.js';
import { ASTParser } from '../js/fs/astparser.js';
import { initFormalSystem } from '../js/fs/initial.js';

const parser = new ASTParser(), mgr = new ASTMgr();
const parse = text => parser.parse(text);
const text = ast => parser.stringifyTight(ast);
const nfName = /^#v*nf$/;
const apply = (fs, name, values, conditions = []) => fs.deduct({
    deductionIdx: name, replaceValues: values.map(parse), conditionIdxs: conditions
});
function withoutNf(ast) {
    if (ast.type === 'fn' && nfName.test(ast.name)) return withoutNf(ast.nodes[0]);
    return { ...ast, ...(ast.nodes && { nodes: ast.nodes.map(withoutNf) }) };
}
function instantiate(ast, table) {
    const out = mgr.clone(ast);
    mgr.replaceByMatchTable(out, Object.fromEntries(Object.entries(table).map(([k, v]) => [k, parse(v)])));
    return out;
}
// Independent, concrete, quantifier-free substitution oracle. No assertion
// engine, fuzzy equality or production replacement scanner is used here.
function referenceReplace(body, source, destination, index) {
    const result = mgr.clone(body);
    let count = 0;
    const walk = node => {
        if (mgr.equal(node, source)) {
            count++;
            if (index === 0 || count === Math.abs(index)) mgr.assign(node, destination);
            return;
        }
        for (const child of index < 0 ? [...(node.nodes ?? [])].reverse() : node.nodes ?? []) walk(child);
    };
    walk(result);
    return result;
}

test('a8 replaces the first compound occurrence after an nf-wrapped atom', () => {
    const fs = initFormalSystem(true).fs;
    const atom = '#nf($a,x)';
    const idx = apply(fs, 'a8', [`cos(${atom})`, '0', `(sin(${atom}),cos(${atom}))=x`, '1']);
    assert.equal(text(fs.propositions[idx].value),
        `(cos(${atom})=0)>(((sin(${atom}),cos(${atom}))=x)>((sin(${atom}),0)=x))`);
    assert.equal(fs.propositions[idx].from.deductionIdx, 'a8');
    assert.equal(fs.propositions.some(p => !p.from), false, 'no hypotheses were introduced');
});

test('both scanners skip only proven strict outer terms and preserve occurrence counts', () => {
    const a = new AssertionSystem();
    const atom = '#nf($a,x)', source = `cos(${atom})`;
    const body = `(sin(${atom}),(cos(${atom}),cos(${atom})))=x`;
    for (const index of [0, 1, 2, 3, -1, -2, -3]) {
        const nth = index === 0 ? -1 : Math.abs(index) - 1;
        const scopes = a.getSubAstMatchTimes(parse(body), parse(source), nth, parse('0'), [], [], index < 0);
        assert.ok(scopes, `read-only scanner must decide ${index}`);
        const ast = parse(`#rp((${body}),${source},0,${index})`);
        a.expand(ast, false);
        const expected = referenceReplace(withoutNf(parse(body)), withoutNf(parse(source)), parse('0'), index);
        assert.equal(text(withoutNf(ast)), text(expected), `occurrence ${index}`);
        assert.match(text(ast), /#nf\(\$a,x\)/, 'unreplaced assertions survive');
    }
});

test('uncertain identities, assertion metadata and opaque operators are not absence proofs', () => {
    const a = new AssertionSystem(), atom = parse('#nf($a,x)');
    for (const source of ['cos($b)', 'cos(#nf($b,$a))', '#nf($a,x)', '$a',
        '#rp(cos($a),cos($a),0)', '#crp(cos($a),$b,0)', '$f($a)', 'V$a:($b=$b)']) {
        assert.equal(a.nfAtomCannotContain(atom, parse(source)), false, source);
    }
    for (const source of ['cos($b)', 'cos(#nf($b,$a))']) {
        const body = parse(`sin(#nf($a,x))`);
        assert.equal(a.getSubAstMatchTimesAndReplace(body, parse(source), parse('0'), 0, [], [], false), false);
        assert.equal(text(body), 'sin(#nf($a,x))', 'unknown scans must roll back');
    }
    assert.equal(a.nfAtomCannotContain(parse('#nf(cos($a),x)'), parse('cos(cos($a))')), false,
        'the new rule intentionally handles wrapped atoms only');
});

test('nested nf and vnf wrappers work without using their annotation arguments', () => {
    const a = new AssertionSystem();
    for (const atom of ['#nf(#nf($a,x),y)', '#vnf($a,z,x)', '#nf(#vnf($a,z,x),y)']) {
        const ast = parse(`#rp((sin(${atom}),cos(${atom})),cos(${atom}),0,1)`);
        a.expand(ast, true);
        assert.equal(text(withoutNf(ast)), '(sin($a),0)', atom);
        assert.match(text(ast), /#(?:v*)nf/);
    }
});

test('wrapper differences never certify a missed occurrence or an unsafe crp', () => {
    const a = new AssertionSystem();
    for (const [left, right] of [
        ['cos(#nf($a,x))', 'cos($a)'],
        ['cos($a)', 'cos(#nf($a,x))'],
        ['cos(#nf($a,x))', 'cos(#nf($a,y))']
    ]) {
        for (const nth of [-1, 0]) {
            assert.equal(a.getSubAstMatchTimes(parse(left), parse(right), nth, parse('y')), false);
            const candidate = parse(left);
            assert.equal(a.getSubAstMatchTimesAndReplace(candidate, parse(right), parse('y'), nth, [], [], false), false);
            assert.equal(text(candidate), left);
            assert.equal(a.crp(parse(left), parse(right), parse('y'), nth, false, {}), 0,
                'uncertainty must remain unknown, including replace-all');
        }
    }
    const ast = parse('#rp((sin($a),(cos($b),cos(#nf($b,x)))),cos($b),0,-1)');
    a.expand(ast, true);
    assert.equal(ast.name, '#rp', 'the last occurrence cannot be selected before wrapper aliases are known');
    assert.equal(a.getSubAstMatchTimes(parse('#nf($a,x)'), parse('f(#nf($b,y))'), -1,
        parse('#nf($a,x)'), [parse('y')]), false,
    'dst equaling the current node cannot certify unknown nested substitutions under a binder');
});

test('newly simplified results commute with ground specialization and an independent oracle', () => {
    const a = new AssertionSystem();
    let checks = 0;
    for (const atom of ['$a', '#nf($a,x)', '#nf(#nf($a,x),y)', '#vnf($a,y,x)']) {
        for (const source of [`cos(${atom})`, `S(${atom})`, `${atom}+0`, `f(g(${atom}))`, `(${atom},0)`, 'cos($b)']) {
            const body = `(sin(${atom}),(${source},cos(#nf($b,x))))=x`;
            for (const index of [0, 1, 2, -1, -2]) {
                const symbolic = parse(`#rp((${body}),${source},0,${index})`);
                a.expand(symbolic, false);
                for (const av of ['a', 'cos(a)', '(a,b)']) for (const bv of ['a', 'cos(a)', 'b']) {
                    const table = { '$a': av, '$b': bv };
                    const concrete = instantiate(symbolic, table);
                    a.expand(concrete, false);
                    const expected = referenceReplace(withoutNf(instantiate(parse(body), table)),
                        withoutNf(instantiate(parse(source), table)), parse('0'), index);
                    assert.equal(text(concrete), text(expected), JSON.stringify({ atom, source, index, av, bv }));
                    checks++;
                }
            }
        }
    }
    assert.equal(checks, 1080);
});

test('capture, violated nf assertions and bound occurrences cannot be used to forge conclusions', () => {
    for (const [name, values] of [
        ['a4', ['x', 'Ey:(x=y)', 'y']],
        ['a6', ['x=x', 'x']],
        ['a8', ['cos(#nf($a,x,y))', 'y', 'Vy:((sin(#nf($a,x,y)),cos(#nf($a,x,y)))=y)', '1']],
        ['a8', ['cos(#nf(x,x))', '0', '(sin(#nf(x,x)),cos(#nf(x,x)))=x', '1']]
    ]) {
        const fs = initFormalSystem(true).fs;
        assert.throws(() => apply(fs, name, values), /Assertion failed|断言失败/);
        assert.equal(fs.propositions.length, 0, 'failed inference must leave no theorem');
    }
    const a = new AssertionSystem();
    const ast = parse('#rp(Vx:(x=x),x,0,1)');
    a.expand(ast, false);
    assert.equal(text(ast), '(Vx:(x=x))', 'bound occurrences are not free occurrences');
});

test('recording and specializing the repaired a8 instance cannot erase nf restrictions', () => {
    const fs = initFormalSystem(true).fs;
    apply(fs, 'a8', ['cos(#nf($a,x))', '0', '(sin(#nf($a,x)),cos(#nf($a,x)))=x', '1']);
    fs.addMacro('nfRegression', 'user*');
    assert.deepEqual(fs.generateDeduction('nfRegression').replaceNames, ['$a']);
    const before = fs.propositions.length;
    assert.throws(() => apply(fs, 'nfRegression', ['x']), /Assertion failed|断言失败/);
    assert.equal(fs.propositions.length, before);
    const i = apply(fs, 'nfRegression', ['0']);
    assert.equal(text(fs.propositions[i].value), '(cos(0)=0)>(((sin(0),cos(0))=x)>((sin(0),0)=x))');
});

// A two-element first-order model, independent of production matching and
// simplification. Every unary/binary function table is allowed, including
// constant, identity and cyclic functions; equality is actual domain equality.
function evaluate(ast, model, env) {
    if (ast.type === 'replvar') return env[ast.name];
    const v = ast.nodes.map(n => evaluate(n, model, env));
    if (ast.name === '=') return v[0] === v[1];
    if (ast.name === '>') return !v[0] || v[1];
    if (ast.name === '~') return !v[0];
    if (ast.name === 'sin' || ast.name === 'cos') return (model[ast.name] >> v[0]) & 1;
    if (ast.name === '(') return (model.pair >> (2 * v[0] + v[1])) & 1;
    throw new Error('Unsupported model expression: ' + text(ast));
}
test('repaired a8 is true in every two-element interpretation of the example functions', () => {
    const fs = initFormalSystem(true).fs;
    const idx = apply(fs, 'a8', ['cos(#nf($a,x))', '$b', '(sin(#nf($a,x)),cos(#nf($a,x)))=x', '1']);
    const formula = withoutNf(fs.propositions[idx].value);
    let checks = 0;
    for (let sin = 0; sin < 4; sin++) for (let cos = 0; cos < 4; cos++) for (let pair = 0; pair < 16; pair++) {
        for (let av = 0; av < 2; av++) for (let bv = 0; bv < 2; bv++) for (let x = 0; x < 2; x++) {
            assert.equal(evaluate(formula, { sin, cos, pair }, { '$a': av, '$b': bv, x }), true);
            checks++;
        }
    }
    assert.equal(checks, 2048);
});

test('bounded adversarial proof search cannot derive an arbitrary proposition or explode a contradiction', t => {
    const fs = initFormalSystem(true).fs;
    const known = new Map();
    let attempts = 0, rejected = 0;
    function attempt(name, values, conditions = []) {
        attempts++;
        let index;
        try { index = apply(fs, name, values, conditions); }
        catch { rejected++; return; }
        const value = fs.propositions[index].value;
        assert.ok(!(value.type === 'replvar' && value.name.startsWith('$')),
            `FORGED ARBITRARY PROPOSITION via ${name}: ${text(value)}`);
        const key = text(value);
        if (known.has(key)) fs.propositions.pop();
        else known.set(key, index);
    }
    // All seeds come from the actual inference engine, without user axioms,
    // assumptions, fabricated proposition records or trusted proof shortcuts.
    const formulas = ['$0', '~$0', '$0>$0', 'x=x', '~(x=x)', '(x=x)>$0'];
    for (const p of formulas) {
        attempt('.i', [p]);
        attempt('.ne', [p]);
        for (const q of ['$0', 'x=x']) {
            attempt('a1', [p, q]);
            attempt('a3', [p, q]);
            attempt('a2', [p, q, '$0']);
        }
    }
    for (const atom of ['$a', '#nf($a,x)', '#nf(#nf($a,x),y)']) {
        const source = `cos(${atom})`;
        attempt('a7', [source]);
        for (const destination of ['0', source, '$b']) {
            for (const body of [`(sin(${atom}),${source})=x`, `~(${source}=${source})`]) {
                for (const n of ['0', '1', '-1']) attempt('a8', [source, destination, body, n]);
            }
        }
    }
    // Two breadth rounds, at most 256 distinct theorems. Every pair is tried
    // through mp and contradiction elimination with the explicit target $0.
    const limit = 256;
    for (let round = 0; round < 2 && known.size < limit; round++) {
        const indices = [...known.values()];
        for (const left of indices) {
            for (const right of indices) {
                if (known.size >= limit) break;
                attempt('mp', [], [left, right]);
                attempt('.m', ['$0'], [left, right]);
            }
            if (known.size >= limit) break;
        }
    }
    assert.ok(attempts > 1000, 'search must actually exercise failed proof attempts');
    assert.ok(rejected > 1000);
    assert.ok(fs.propositions.every(p => p.from), 'all propositions must have inference provenance');
    let modelChecks = 0;
    for (const p of fs.propositions) {
        const formula = withoutNf(p.value);
        for (let sin = 0; sin < 4; sin++) for (let cos = 0; cos < 4; cos++) for (let pair = 0; pair < 16; pair++) {
            for (let av = 0; av < 2; av++) for (let bv = 0; bv < 2; bv++) for (let x = 0; x < 2; x++) {
                for (const proposition of [false, true]) {
                    assert.equal(evaluate(formula, { sin, cos, pair },
                        { '$a': av, '$b': bv, x, '$0': proposition, '0': 0 }), true, text(p.value));
                    modelChecks++;
                }
            }
        }
    }
    t.diagnostic(`${attempts} actual inference attempts, ${rejected} rejected, ${known.size} distinct theorems; two rounds, theorem cap ${limit}`);
    t.diagnostic(`${modelChecks} independent model checks of all accepted theorems, including valuations where $0 is false`);
});

function identityApply(fs, name, conditions = []) {
    return apply(fs, name, fs.generateDeduction(name).replaceNames, conditions);
}
const hypotheses = fs => fs.propositions.filter(p => !p.from);

test('a contradiction recorded, nested, expanded and discharged never loses its hypotheses', () => {
    const fs = initFormalSystem(true).fs;
    fs.fastmetarules = 'cvuqe><:#zZQR';
    fs.addHypothese(parse('$p'));
    fs.addHypothese(parse('~$p'));
    apply(fs, '.m', ['$0'], [0, 1]);
    fs.addMacro('explosion0', 'user*');
    for (let level = 0; level < 6; level++) {
        const name = 'explosion' + level;
        assert.equal(fs.generateDeduction(name).conditions.length, 2);
        for (const mode of [null, 'deep']) {
            fs.expandMacroWithDefaultValue(name, mode);
            assert.deepEqual(hypotheses(fs).map(p => text(p.value)), ['$p', '~$p']);
            assert.equal(text(fs.propositions.at(-1).value), '$0', 'legal only with the two contradictory assumptions');
        }
        fs.removePropositions();
        assert.throws(() => identityApply(fs, name), /condition|条件/);
        assert.equal(fs.propositions.length, 0);
        fs.addHypothese(parse('$p'));
        fs.addHypothese(parse('~$p'));
        const index = identityApply(fs, name, [0, 1]);
        fs.inlineMacroInProp(index);
        assert.equal(hypotheses(fs).length, 2);
        fs.addMacro('explosion' + (level + 1), 'user*');
    }
    for (const [name, conditions, conclusion] of [
        ['explosion6', 2, '$0'], ['>explosion6', 1, '~$p>$0'], ['>>explosion6', 0, '$p>(~$p>$0)']
    ]) {
        const rule = fs.generateDeduction(name);
        assert.equal(rule.conditions.length, conditions);
        assert.equal(text(rule.conclusion), conclusion);
    }
    fs.removePropositions();
    identityApply(fs, '>>explosion6');
    fs.addMacro('closedExplosion', 'user*');
    fs.expandMacroWithDefaultValue('closedExplosion', 'deep');
    assert.equal(hypotheses(fs).length, 0);
    assert.equal(text(fs.propositions.at(-1).value), '$p>(~$p>$0)');
    for (const p of [false, true]) for (const goal of [false, true]) {
        assert.equal(evaluate(fs.propositions.at(-1).value, {}, { '$p': p, '$0': goal }), true);
    }
    const last = fs.propositions.length - 1;
    assert.throws(() => apply(fs, 'mp', [], [last, last]));
    assert.throws(() => apply(fs, '.m', ['$0'], [last, last]));
    assert.ok(fs.propositions.every(p => text(p.value) !== '$0'));
});

test('nf replacement rules retain conditions and restrictions through recording, expansion and further inference', () => {
    for (const atom of ['#nf($a,x)', '#nf(#nf($a,x),y)', '#vnf($a,y,x)']) {
        const source = `cos(${atom})`, body = `(sin(${atom}),${source})=x`;
        for (const destination of ['0', source, '$b']) {
            const fs = initFormalSystem(true).fs;
            fs.fastmetarules = 'cvuqe><:#zZQR';
            const assumptions = [`${source}=${destination}`, body];
            assumptions.forEach(h => fs.addHypothese(parse(h)));
            const axiom = apply(fs, 'a8', [source, destination, body, '1']);
            const implication = apply(fs, 'mp', [], [axiom, 0]);
            apply(fs, 'mp', [], [implication, 1]);
            fs.addMacro('conditionalNf', 'user*');
            const signature = text(fs.generateDeduction('conditionalNf').value);
            for (const mode of [null, 'deep']) {
                fs.expandMacroWithDefaultValue('conditionalNf', mode);
                assert.equal(hypotheses(fs).length, 2);
                fs.addMacro(mode ? 'deepNf' : 'shallowNf', 'user*');
                assert.equal(text(fs.generateDeduction(mode ? 'deepNf' : 'shallowNf').value), signature);
            }
            fs.removePropositions();
            assert.throws(() => identityApply(fs, 'deepNf'), /condition|条件/);
            assert.equal(fs.propositions.length, 0);
            assumptions.forEach(h => fs.addHypothese(parse(h)));
            const index = identityApply(fs, 'shallowNf', [0, 1]);
            fs.inlineMacroInProp(index);
            assert.equal(hypotheses(fs).length, 2);
            fs.addMacro('inlinedNf', 'user*');
            assert.equal(text(fs.generateDeduction('inlinedNf').value), signature);
            const closed = fs.generateDeduction('>>inlinedNf');
            assert.equal(closed.conditions.length, 0);
            assert.equal(closed.conclusion.name, '>', 'discharged assumptions remain as antecedents');
            fs.removePropositions();
            identityApply(fs, '>>inlinedNf');
            fs.addMacro('closedNf', 'user*');
            fs.expandMacroWithDefaultValue('closedNf', 'deep');
            assert.equal(hypotheses(fs).length, 0);
            assert.equal(text(fs.propositions.at(-1).value), text(closed.conclusion));
            const formula = withoutNf(fs.propositions.at(-1).value);
            for (let sin = 0; sin < 4; sin++) for (let cos = 0; cos < 4; cos++) for (let pair = 0; pair < 16; pair++) {
                for (let av = 0; av < 2; av++) for (let bv = 0; bv < 2; bv++) for (let x = 0; x < 2; x++) {
                    assert.equal(evaluate(formula, { sin, cos, pair }, { '$a': av, '$b': bv, x, '0': 0 }), true,
                        'the fully discharged, deeply expanded rule must hold even when its assumptions are false');
                }
            }
            const last = fs.propositions.length - 1;
            assert.throws(() => apply(fs, '.m', ['$0'], [last, last]));
            const invalid = fs.generateDeduction('closedNf').replaceNames.map(n => n === '$a' ? 'x' : n);
            const before = fs.propositions.length;
            assert.throws(() => apply(fs, 'closedNf', invalid), /Assertion failed|断言失败/);
            assert.equal(fs.propositions.length, before);
            assert.ok(fs.propositions.every(p => text(p.value) !== '$0'));
        }
    }
});
