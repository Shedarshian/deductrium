import assert from 'node:assert/strict';
import test from 'node:test';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { initFormalSystem } from '../js/fs/initial.js';
import { SavesParser } from '../js/fs/savesparser.js';
import { ASTParser } from '../js/fs/astparser.js';
import { RuleParser } from '../js/fs/metarule.js';

const parser = new ASTParser();
const saves = new SavesParser(true);
function system() {
    const { fs } = initFormalSystem(true);
    fs.fastmetarules = 'cvuqe><:#zZQR';
    return fs;
}
const str = ast => parser.stringifyTight(ast);
function chain(fs, count, prefix = 't') {
    for (let i = 0; i < count; i++) {
        saves.deserializeDeduction(prefix + i, fs, ['⊢$0>$0', 'user*', [[i ? prefix + (i - 1) : '.i', [], ['$0']]]]);
    }
    return prefix + (count - 1);
}
function apply(fs, name, mode = null) {
    const d = fs.generateDeduction(name);
    return fs.deduct({ deductionIdx: name, conditionIdxs: [], replaceValues: d.replaceNames.map(n => parser.parse(n)) }, mode);
}

test('loading, applying, recording and saving a macro do not load referenced bodies', () => {
    const fs = system();
    const name = chain(fs, 4000);
    let loads = 0;
    for (const d of Object.values(fs.deductions)) {
        if (d.proof) {
            const load = d.proof.load;
            d.proof.load = () => { loads++; return load(); };
        }
    }
    apply(fs, name);
    fs.addMacro('recorded', 'user*');
    const saved = saves.serializeDeduction(fs.deductions[name]);
    assert.equal(loads, 0);
    assert.equal(saved[2][0][0], 't3998');
    assert.equal(str(fs.propositions[0].value), '$0>$0');
    const generated = fs.generateDeduction('v' + name);
    assert.equal(generated.conclusion.name, 'V');
    assert.equal(loads, 0, 'signature and admissibility analysis must not parse proof bodies');
    assert.ok(generated.proof);
});

test('deep expansion traverses 4000 nested macros without JS recursion', () => {
    const fs = system();
    const name = chain(fs, 4000);
    const start = performance.now();
    apply(fs, name, 'deep');
    assert.equal(fs.propositions.length, 5);
    assert.equal(str(fs.propositions.at(-1).value), '$0>$0');
    assert.ok(fs.proofCache.size <= 128);
    console.log(`4000-layer expansion: ${Math.round(performance.now() - start)} ms`);
});

test('one-level expansion preserves child references', () => {
    const fs = system();
    const name = chain(fs, 20);
    apply(fs, name, 'inline');
    assert.equal(fs.propositions.length, 1);
    assert.equal(fs.propositions[0].from.deductionIdx, 't18');
});

test('the existing save format round-trips lazy user macros and propositions', () => {
    const fs = system();
    const name = chain(fs, 30);
    apply(fs, name);
    const gui = { formalSystem: fs, deductions: [name], metarules: [], getProps: () => fs.propositions };
    const encoded = saves.serialize(gui);
    const restored = system();
    const { arrD } = saves.deserializeArr(restored, JSON.parse(encoded));
    assert.deepEqual(arrD, [name]);
    assert.deepEqual(restored.propositions.map(p => saves.serializeProposition(p)), fs.propositions.map(p => saves.serializeProposition(p)));
    assert.ok(restored.deductions[name].proof);
    restored.expandMacroWithProp(0);
    assert.equal(restored.propositions[0].from.deductionIdx, 't28');
    restored.expandMacroWithDefaultValue(name, 'deep');
    assert.equal(str(restored.propositions.at(-1).value), '$0>$0');
});

test('cycles and budget failures restore propositions, rule table and unlock state', () => {
    const fs = system();
    saves.deserializeDeduction('loop', fs, ['⊢$0>$0', 'user*', [['loop', [], ['$0']]]]);
    fs.addHypothese(parser.parse('A'));
    const oldProps = fs.propositions;
    const before = JSON.stringify(fs.propositions);
    const unlocks = fs.fastmetarules;
    assert.throws(() => fs.expandMacroWithDefaultValue('loop', 'deep'), /Cyclic/);
    assert.equal(fs.propositions, oldProps);
    assert.equal(JSON.stringify(fs.propositions), before);
    const name = chain(fs, 20);
    fs.evaluationLimits.operations = 5;
    const names = Object.keys(fs.deductions);
    assert.throws(() => fs.expandMacroWithDefaultValue(name, 'deep'), /budget/);
    assert.equal(JSON.stringify(fs.propositions), before);
    assert.deepEqual(Object.keys(fs.deductions), names);
    assert.equal(fs.fastmetarules, unlocks);
    fs.evaluationLimits.operations = 50_000;
    fs.expandMacroWithDefaultValue('.i', 'deep');
    assert.equal(str(fs.propositions.at(-1).value), '$0>$0');
});

test('proof output explosion is bounded and rolls back atomically', () => {
    const fs = system();
    for (let i = 0; i < 16; i++) {
        const dependency = i ? 'b' + (i - 1) : '.i';
        saves.deserializeDeduction('b' + i, fs, ['⊢$0>$0', 'user*', [[dependency, [], ['$0']], [dependency, [], ['$0']]]]);
    }
    fs.evaluationLimits.operations = 1000;
    assert.throws(() => apply(fs, 'b15', 'deep'), /budget/);
    assert.equal(fs.propositions.length, 0);
});

test('deep rule expressions stop cleanly and the parser remains reusable', () => {
    const rules = new RuleParser();
    assert.throws(() => rules.parse('c'.repeat(4000) + '.i'), /depth exceeded/);
    assert.deepEqual(rules.parse('c.i'), ['c', ['.i']]);
    const fs = system();
    assert.throws(() => fs.generateDeduction('c'.repeat(4000) + '.i'), /depth exceeded/);
    assert.ok(fs.generateDeduction('c.i'));
});

test('lazy macros retain identity under axiom-only quantification and reject invalid primitives', () => {
    const fs = system();
    fs.fastmetarules = 'q';
    assert.equal(fs.generateDeduction('va1').conclusion.name, 'V');
    assert.throws(() => fs.generateDeduction('v.i'));
    fs.fastmetarules = 'cvuqe><:#zZQR';
    assert.throws(() => fs.generateDeduction('>mp'));
    assert.throws(() => fs.generateDeduction('e.t'));
    assert.throws(() => fs.generateDeduction('<a7'));
    fs.addDeduction('unknown', parser.parse('$0⊢$1'), 'custom');
    assert.throws(() => fs.generateDeduction('cunknown'));
    assert.throws(() => fs.generateDeduction('vunknown'));
});

test('renaming and deleting inspect lazy dependencies and invalidate generated signatures', () => {
    const fs = system();
    chain(fs, 2);
    fs.generateDeduction('ct1');
    fs.renameDeduction('t0', 'renamed');
    assert.equal(fs.deductions.ct1, undefined);
    assert.equal(saves.serializeDeduction(fs.deductions.t1)[2][0][0], 'renamed');
    assert.throws(() => fs.removeDeduction('renamed'));
    fs.removeDeduction('t1');
    fs.removeDeduction('renamed');
    assert.equal(fs.deductions.renamed, undefined);
});

test('derived rule cache stays bounded and evicted entries can be regenerated', () => {
    const fs = system();
    for (let i = 1; i < 650; i++) fs.generateDeduction('.' + i + '@N');
    assert.ok(fs.generated.size <= 512);
    assert.ok(fs.deductions['.1@N'] === undefined);
    assert.equal(str(fs.generateDeduction('.1@N').conclusion), '1@N');
    assert.ok(fs.deductions['.i']);
});

test('every builtin macro can materialize c/v recipes with the advertised signature', () => {
    const fs = system();
    const names = Object.keys(fs.deductions).filter(name => fs.isMacro(fs.deductions[name]));
    for (const name of names) {
        for (const op of ['c', 'v']) {
            const rule = fs.generateDeduction(op + name);
            assert.ok(fs.getProofSteps(rule)?.length, op + name);
        }
    }
    assert.equal(names.length, 195);
});

test('inlining updates later indices without mutating preview snapshots', () => {
    const fs = system();
    apply(fs, '.i');
    fs.deduct({ deductionIdx: '<a1', conditionIdxs: [0], replaceValues: [parser.parse('B')] });
    const original = fs.propositions[1];
    fs.inlineMacroInProp(0);
    assert.deepEqual(original.from.conditionIdxs, [0]);
    assert.deepEqual(fs.propositions.at(-1).from.conditionIdxs, [4]);
    assert.equal(str(fs.propositions.at(-1).value), 'B>($0>$0)');
});

test('small proofs match the previous implementation in signature, parameter order and expansion', async () => {
    // Read-only baseline extraction. The historical commit is fixed so this
    // remains a real compatibility check after merging the change into main.
    const directory = mkdtempSync(join(tmpdir(), 'deductrium-proof-baseline-'));
    try {
        const archive = execFileSync('git', ['archive', '62c2a81', 'js'], { maxBuffer: 16 * 1024 * 1024 });
        execFileSync('tar', ['-xf', '-', '-C', directory], { input: archive });
        const baseline = await import(pathToFileURL(join(directory, 'js/fs/initial.js')));
        const old = baseline.initFormalSystem(true).fs;
        old.fastmetarules = 'cvuqe><:#zZQR';
        const fs = system();
        for (const name of ['c.t', '>.t', 'v.i', 'u.t', 'e.cs', '<a1', ':a1,mp', 'vc.t', 'cv.t', 'vv.i', 'c.ni', 'v.ni', 'c.cs', 'v.cs', 'v<.<>1', 'v<<a8', '>c.t', 'c.Vnf', 'v.Vnf', 'c.Enf', 'v.Enf', 'v.Vnf>', 'c.Vnf>']) {
            const expected = old.generateDeduction(name);
            const actual = fs.generateDeduction(name);
            assert.equal(str(actual.value), str(expected.value), name + ' signature');
            assert.deepEqual(actual.replaceNames, expected.replaceNames, name + ' replacement order');
            assert.deepEqual(actual.replaceTypes, expected.replaceTypes, name + ' replacement types');
            old.expandMacroWithDefaultValue(name);
            fs.expandMacroWithDefaultValue(name);
            assert.deepEqual(fs.propositions.map(p => str(p.value)), old.propositions.map(p => str(p.value)), name + ' one-level proof');
            fs.expandMacroWithDefaultValue(name, 'deep');
            assert.equal(str(fs.propositions.at(-1).value), str(expected.conclusion), name + ' deep conclusion');
        }
    } finally {
        // directory is a fresh mkdtemp child of the OS temporary directory.
        assert.ok(directory.startsWith(join(tmpdir(), 'deductrium-proof-baseline-')));
        rmSync(directory, { recursive: true, force: true });
    }
});
