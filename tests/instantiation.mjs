import assert from 'node:assert/strict';
import test from 'node:test';
import { initFormalSystem } from '../js/fs/initial.js';
import { ASTParser } from '../js/fs/astparser.js';
import { ASTMgr } from '../js/fs/astmgr.js';
import { instantiateQuantifiers } from '../js/fs/instantiate.js';
import { ruleCommand, withCommandDom } from './command-harness.mjs';

const parser = new ASTParser(), mgr = new ASTMgr();
const parse = text => parser.parse(text), text = ast => parser.stringifyTight(ast);
function system(formula) {
    const { fs } = initFormalSystem(true);
    fs.fastmetarules = 'cvuqe><:#zZQR';
    if (formula) fs.addHypothese(parse(formula));
    return fs;
}
function apply(fs, rule, values = [], conditions = []) {
    return fs.deduct({ deductionIdx: rule, replaceValues: values.map(parse), conditionIdxs: conditions });
}
function replay(fs) {
    const saved = structuredClone(fs.propositions);
    fs.removePropositions();
    for (const p of saved) {
        if (p.from) fs.deduct(p.from);
        else fs.addHypothese(p.value);
        assert.ok(mgr.equal(fs.propositions.at(-1).value, p.value), 'each visible step must replay through the kernel');
    }
}
function boundNames(ast, out = []) {
    if (ast.type === 'sym' && ['V', 'E'].includes(ast.name)) out.push(ast.nodes[0]);
    for (const child of ast.nodes ?? []) boundNames(child, out);
    return out;
}

test('interleaved universals and antecedents produce checked steps and ordered assumptions', async () => {
    const fs = system('Vg:Vr:((g=r)>Vx:((x@g)>Ey:((y@g)&(y=x))))');
    const original = fs.propositions, before = structuredClone(original);
    const result = await instantiateQuantifiers(fs, 0);
    assert.equal(result.steps, 9);
    assert.equal(result.assumptions, 2);
    assert.deepEqual(original, before, 'insertion/reindexing must not mutate original proposition objects');
    assert.equal(text(fs.propositions.at(-1).value), '(E$y:(($y@#nf($g,$y))&($y=#nf($x,$y))))');
    assert.deepEqual(fs.propositions.filter(p => !p.from).slice(1).map(p => text(p.value)),
        ['#nf($g,$y)=$r', '#nf($x,$y)@#nf($g,$y)']);
    assert.deepEqual(fs.propositions.filter(p => p.from).map(p => p.from.deductionIdx),
        ['vvcvc.Ecn', 'vvc.Vcn', 'v.Vcn', '<a4', '<a4', 'mp', '<a4', 'mp', '.Ecn']);
    replay(fs);
});

test('existentials in either conjunction branch preserve order and require no user helper theorem', async () => {
    for (const formula of [
        'Vx:((x=x)&Ey:((x=y)&Ez:(z=y)))',
        'Vx:((Ey:((x=y)&Ez:(z=y)))&(x=x))',
        'Vx:((Ey:(x=y))&(Ez:(x=z)))',
        'Vx:((x=x)&((Ey:(x=y))&(Ez:(x=z))))'
    ]) {
        const fs = system(formula);
        const result = await instantiateQuantifiers(fs, 0);
        assert.equal(result.assumptions, 0);
        assert.equal(fs.propositions.at(-1).value.name, '&');
        assert.ok(fs.propositions.some(p => p.from?.deductionIdx.includes('::<a1')));
        assert.ok(fs.propositions.every(p => !p.from?.deductionIdx.includes('s&>')));
        const original = fs.propositions[0].value.nodes[1];
        const final = fs.propositions.at(-1).value;
        assert.equal(original.name, final.name);
        assert.deepEqual(original.nodes.map(n => n.name), final.nodes.map(n => n.name));
        replay(fs);
    }
});

test('nf constraints follow lexical occurrences, omitting unrelated later E scopes', async () => {
    const fs = system('Vx:Vu:Ey:((x=y)&Ez:(u=z))');
    await instantiateQuantifiers(fs, 0);
    const final = text(fs.propositions.at(-1).value);
    assert.match(final, /#nf\(\$x,\$y\)/);
    assert.ok(!final.includes('#nf($x,$y,$z)'));
    assert.match(final, /#nf\(\$u,\$y,\$z\)/);
    assert.ok(!final.includes('#nf($y,$z)'), 'y is not used inside Ez');
    assert.ok(!final.includes('#nf($z,$y)'), 'inner E does not need a backward nf constraint');
    replay(fs);
    const mutual = system('Vx:Ey:Ez:((x=y)&(y=z))');
    await instantiateQuantifiers(mutual, 0);
    const mutualText = text(mutual.propositions.at(-1).value);
    assert.match(mutualText, /#nf\(\$y,\$z\)/);
    assert.ok(!mutualText.includes('#nf($z,$y)'));
    replay(mutual);
});

test('shadowed binder spellings become different parameters and keep distinct scopes', async () => {
    const fs = system('Vx:Ex:(x=x)');
    await instantiateQuantifiers(fs, 0);
    assert.equal(text(fs.propositions.at(-1).value), '(E$x1:($x1=$x1))');
    assert.equal(fs.propositions.find(p => p.from?.deductionIdx === '<a4').from.replaceValues[0].name, '$x');
    replay(fs);
});

test('the first E is alpha-converted even without a preceding V', async () => {
    const fs = system('Ey:Ez:(y=z)');
    await instantiateQuantifiers(fs, 0);
    assert.equal(fs.propositions.find(p => p.from).from.deductionIdx, 'e.Ecn');
    assert.equal(fs.propositions.filter(p => p.from)[1].from.deductionIdx, '.Ecn');
    assert.equal(text(fs.propositions.at(-1).value), '(E#nf($y,$z):(E$z:(#nf($y,$z)=$z)))');
    replay(fs);
});

test('existing local binders are retained unless they collide with another binder', async () => {
    const fs = system('Vx:Ey:Ey:(y=y)');
    const first = apply(fs, 've.Ecn', ['#y'], [0]);
    const second = apply(fs, 'v.Ecn', ['#y'], [first]);
    const start = fs.propositions.length;
    const result = await instantiateQuantifiers(fs, second);
    assert.ok(fs.propositions.slice(start).some(p => p.from?.replaceValues[0]?.name.startsWith('#y')));
    assert.equal(new Set(boundNames(fs.propositions[result.index].value).map(b => fs.assert.getVarName(b))).size, 2);
    replay(fs);
});

test('fresh local names avoid names already present elsewhere in the proof', async () => {
    const fs = system('Vx:Vy:(x=y)');
    apply(fs, 'v.Vcn', ['#y'], [0]);
    const start = fs.propositions.length;
    await instantiateQuantifiers(fs, 0);
    assert.equal(fs.propositions[start].from.replaceValues[0].name, '#y1');
    replay(fs);
});

test('generated hypotheses reindex existing proofs without corrupting their provenance', async () => {
    const fs = system('Vx:((x=x)>(x=x))');
    apply(fs, '.i', ['x=x']);
    const saved = structuredClone(fs.propositions);
    const oldObjects = fs.propositions.slice();
    const result = await instantiateQuantifiers(fs, 0);
    assert.equal(result.assumptions, 1);
    assert.equal(text(fs.propositions[result.index].value), '$x=$x');
    assert.deepEqual(oldObjects, saved);
    replay(fs);
});

test('invalid syntax, dollar variables, unsupported quantifier contexts and capture are rejected atomically', async () => {
    for (const formula of ['V$x:($x=$x)', 'Vx:Ey:((x=y)>Ez:(z=y))', '(Vx:(x=x))>(Ey:(y=y))',
        'E!x:(x=x)', 'Ey:(x=y)', 'Vx:Ey:((y@N)&(x=y))', 'Vx:Ey:(y=0)', 'Vx:Ey:(y={})']) {
        const fs = system(formula);
        const original = fs.propositions, saved = structuredClone(original);
        await assert.rejects(instantiateQuantifiers(fs, 0));
        assert.equal(fs.propositions, original);
        assert.deepEqual(fs.propositions, saved, formula);
    }
});

test('Esc, locked transformations, changed state and kernel failures restore the original proof', async () => {
    for (const failure of ['abort', 'locked', 'state', 'budget']) {
        const fs = system('Vx:((x=x)>Vy:(y=x))');
        const original = fs.propositions, saved = structuredClone(original);
        const controller = new AbortController();
        if (failure === 'locked') fs.fastmetarules = '';
        if (failure === 'budget') fs.evaluationLimits.operations = 1;
        await assert.rejects(instantiateQuantifiers(fs, 0, {
            signal: controller.signal,
            isCurrent: () => failure !== 'state',
            onProgress: () => { if (failure === 'abort') controller.abort(); }
        }));
        assert.equal(fs.propositions, original);
        assert.deepEqual(fs.propositions, saved, failure);
    }
});

test('valid closed theorems remain closed through recording and deep expansion; invalid nf specialization is refused', async () => {
    const fs = system();
    const reflexive = apply(fs, 'a7', ['$x']);
    apply(fs, '.Ei', ['y'], [reflexive]);
    fs.addMacro('existentialReflexivity', 'test*');
    fs.removePropositions();
    const rule = fs.generateDeduction('vexistentialReflexivity');
    const values = rule.replaceNames.map(n => n === '$x' ? 'x' : 'x');
    const source = apply(fs, 'vexistentialReflexivity', values);
    assert.equal(text(fs.propositions[source].value), '(Vx:(Ey:(x=x)))');
    await instantiateQuantifiers(fs, source);
    assert.ok(fs.propositions.every(p => p.from), 'no assumptions may appear in this closed proof');
    fs.addMacro('autoReflexivity', 'test*');
    const auto = fs.generateDeduction('autoReflexivity');
    assert.equal(auto.conditions.length, 0);
    const expected = text(auto.conclusion);
    fs.expandMacroWithDefaultValue('autoReflexivity', 'deep');
    assert.equal(text(fs.propositions.at(-1).value), expected);
    assert.ok(fs.propositions.every(p => p.from));
    const before = structuredClone(fs.propositions);
    assert.throws(() => apply(fs, 'autoReflexivity', auto.replaceNames.map(() => 'z')), /Assertion failed|断言失败/);
    assert.deepEqual(fs.propositions, before);
    const last = fs.propositions.length - 1;
    assert.throws(() => apply(fs, '.m', ['$0'], [last, last]));
    assert.ok(fs.propositions.every(p => text(p.value) !== '$0'));
});

test('button command accepts only complete propositions, supports keyboard input, and cancels safely', async () => {
    await withCommandDom(async () => {
        const fs = system('Vx:Vy:(x=y)');
        const cmd = ruleCommand(fs, ['inst']); cmd.gui.unlockedHyp = true;
        await cmd.execCmdBuffer();
        const before = structuredClone(fs.propositions);
        await cmd.onClickSubAst('p0', 'x=y');
        assert.deepEqual(fs.propositions, before);
        assert.deepEqual(cmd.cmdBuffer, ['inst']);
        await cmd.onClickSubAst('p0', text(fs.propositions[0].value));
        assert.equal(text(fs.propositions.at(-1).value), '$x=$y');
        assert.equal(cmd.gui.actionInput.readOnly, false);
        assert.deepEqual(cmd.cmdBuffer, []);
        const keyboard = ruleCommand(system('Vx:(x=x)'), ['inst', 'p0']); keyboard.gui.unlockedHyp = true;
        await keyboard.execCmdBuffer();
        assert.equal(text(keyboard.gui.formalSystem.propositions.at(-1).value), '$x=$x');
        const cancelled = ruleCommand(system('Vx:Vy:(x=y)'), ['inst', 'p0']); cancelled.gui.unlockedHyp = true;
        const saved = structuredClone(cancelled.gui.formalSystem.propositions);
        const pending = cancelled.execCmdBuffer();
        assert.equal(cancelled.gui.actionInput.readOnly, true);
        cancelled.clearCmdBuffer();
        await pending;
        assert.deepEqual(cancelled.gui.formalSystem.propositions, saved);
        assert.equal(cancelled.gui.actionInput.readOnly, false);
        assert.equal(cancelled.failedQuery, true);
        const unsupported = ruleCommand(system('Vx:Ey:(y=0)'), ['inst', 'p0']); unsupported.gui.unlockedHyp = true;
        const previous = structuredClone(unsupported.gui.formalSystem.propositions);
        await unsupported.execCmdBuffer();
        assert.deepEqual(unsupported.gui.formalSystem.propositions, previous);
        assert.equal(unsupported.failedQuery, true);
        assert.match(unsupported.gui.hintText.innerText, /unchanged|未改动/);
    });
});
