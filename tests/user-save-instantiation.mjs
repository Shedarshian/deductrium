// Optional read-only integration check against the user's existing game save.
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { GameSaveLoad } from '../js/saveload.js';
import { initFormalSystem } from '../js/fs/initial.js';
import { SavesParser } from '../js/fs/savesparser.js';
import { ASTParser } from '../js/fs/astparser.js';
import { instantiateQuantifiers } from '../js/fs/instantiate.js';

const [file] = process.argv.slice(2);
if (!file) throw new Error('Usage: node tests/user-save-instantiation.mjs <save-file>');
const raw = readFileSync(file, 'utf8').replace(/^\uFEFF/, '');
let data;
for (const storageKey of ['deductrium-save', 'deductrium-creative-save']) {
    try { data = JSON.parse(GameSaveLoad.prototype.deserializeStr.call({ storageKey }, raw).split('-(=)-')[2]); break; }
    catch { /* Try the other existing game mode. */ }
}
assert.ok(data);
const parser = new ASTParser();
function system() {
    const { fs } = initFormalSystem(true);
    new SavesParser(true).deserializeArr(fs, structuredClone(data));
    fs.fastmetarules = 'cvuqe><:#zZQR';
    return fs;
}
{
    const fs = system();
    const source = fs.propositions.findIndex(p => p.from && p.value.name === 'V' && !parser.stringifyTight(p.value).includes('$'));
    assert.ok(source >= 0);
    const original = fs.propositions, before = structuredClone(original);
    const expected = parser.stringifyTight(original.at(-1).value);
    const result = await instantiateQuantifiers(fs, source);
    assert.equal(parser.stringifyTight(fs.propositions[result.index].value), expected);
    assert.deepEqual(original, before);
    console.log(JSON.stringify({ case: 'current proof', ...result, originalProofUnchanged: true }));
}
{
    const fs = system();
    fs.removePropositions();
    const recorded = data[4].llinv1;
    assert.ok(recorded?.[2]);
    for (const [deductionIdx, conditionIdxs, values] of recorded[2].slice(0, 2)) {
        await fs.prepareExpansion(deductionIdx);
        fs.deduct({ deductionIdx, conditionIdxs: conditionIdxs.map(i => i < 0 ? fs.propositions.length + i : i),
            replaceValues: values.map(v => parser.parse(v)) });
    }
    const result = await instantiateQuantifiers(fs, fs.propositions.length - 1);
    fs.addMacro('checkedInstantiation', 'test*');
    assert.equal(parser.stringifyTight(fs.deductions.checkedInstantiation.value), parser.stringifyTight(fs.deductions.llinv1.value));
    assert.equal(fs.getProofSteps(fs.deductions.checkedInstantiation).length, recorded[2].length);
    console.log(JSON.stringify({ case: 'llinv1', ...result, matchesOriginalRecordedRule: true, recordedSteps: recorded[2].length }));
}
