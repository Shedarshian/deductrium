// Optional local integration check. The user's save is read in place and is
// never copied into the repository or modified.
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { GameSaveLoad } from '../js/saveload.js';
import { initFormalSystem } from '../js/fs/initial.js';
import { SavesParser } from '../js/fs/savesparser.js';
import { FSCmd } from '../js/fs/cmd.js';

const file = process.argv[2];
const names = process.argv.slice(3);
if (!file || !names.length) throw new Error('Usage: node tests/user-save-expansion.mjs <save-file> <rule> [rule ...]');
const encoded = readFileSync(file, 'utf8').replace(/^\uFEFF/, '');
let data;
for (const storageKey of ['deductrium-save', 'deductrium-creative-save']) {
    try {
        data = JSON.parse(GameSaveLoad.prototype.deserializeStr.call({ storageKey }, encoded).split('-(=)-')[2]);
        break;
    } catch { /* Try the other existing save mode. */ }
}
assert.ok(data, 'save must decode using an existing save format');

function system() {
    const { fs } = initFormalSystem(true);
    new SavesParser(true).deserializeArr(fs, structuredClone(data));
    fs.fastmetarules = 'cvuqe><:#zZQR';
    return fs;
}

for (const name of names) {
    const fs = system(); // Every case starts cold, without manually opening its lemma.
    assert.ok(fs.deductions[name], 'missing user rule: ' + name);
    const loads = [];
    for (const [key, d] of Object.entries(fs.deductions)) {
        if (!d.proof) continue;
        const load = d.proof.load;
        d.proof.load = () => { loads.push(key); return load(); };
    }
    const command = Object.create(FSCmd.prototype);
    Object.assign(command, { cmdBuffer: ['entr', name], escClear: true, pListMasked: false });
    command.gui = {
        formalSystem: fs, isMobile: true, unlockedMacro: true, cmdBtns: [],
        actionInput: { readOnly: false, value: '' }, hintText: { innerText: '', innerHTML: '' },
        getDeduction: id => fs.generateDeduction(id), updatePropositionList() {}
    };
    const started = performance.now();
    await command.execExpand();
    assert.equal(command.cmdBuffer.length, 3, name + ' must enter its preview without a budget error: ' + command.gui.hintText.innerText);
    assert.equal(command.gui.actionInput.readOnly, false);
    assert.ok(fs.propositions.length);
    console.log(JSON.stringify({ name, steps: fs.propositions.length, loadedBodies: loads.length, milliseconds: Math.round(performance.now() - started) }));
}
