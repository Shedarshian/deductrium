// Read an existing local save without modifying or copying it. Exercise the
// actual command handlers with a fresh system for every rule-generation route.
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { GameSaveLoad } from '../js/saveload.js';
import { initFormalSystem } from '../js/fs/initial.js';
import { SavesParser } from '../js/fs/savesparser.js';
import { ASTParser } from '../js/fs/astparser.js';
import { ruleCommand, withCommandDom } from './command-harness.mjs';

const [file, ...names] = process.argv.slice(2);
if (!file || !names.length) throw new Error('Usage: node tests/user-save-rule-queries.mjs <save-file> <base-rule> [base-rule ...]');
const encoded = readFileSync(file, 'utf8').replace(/^\uFEFF/, '');
let data;
for (const storageKey of ['deductrium-save', 'deductrium-creative-save']) {
    try {
        data = JSON.parse(GameSaveLoad.prototype.deserializeStr.call({ storageKey }, encoded).split('-(=)-')[2]);
        break;
    } catch { /* Try the other existing save mode. */ }
}
assert.ok(data);
const parser = new ASTParser();
await withCommandDom(async () => {
    for (const name of names) {
        const results = [];
        for (const kind of ['shortcut', 'explicit', 'mcvt', 'meta-shorthand', 'meta-click']) {
            const { fs } = initFormalSystem(true);
            new SavesParser(true).deserializeArr(fs, structuredClone(data));
            fs.fastmetarules = 'cvuqe><:#zZQR';
            const before = JSON.stringify(fs.propositions);
            const loads = [];
            for (const [key, d] of Object.entries(fs.deductions)) {
                if (!d.proof) continue;
                const load = d.proof.load;
                d.proof.load = () => { loads.push(key); return load(); };
            }
            const target = 'v' + name;
            const buffer = kind === 'shortcut' ? [target] : kind === 'explicit' ? ['d', target] :
                kind === 'meta-shorthand' ? ['mcvt ' + name] : kind === 'meta-click' ? ['meta', 'cvt'] : ['meta', 'cvt', name];
            const cmd = ruleCommand(fs, buffer);
            const started = performance.now();
            await cmd.execCmdBuffer();
            if (kind === 'meta-click') await cmd.onClickSubAst(name, name);
            assert.ok(!cmd.failedQuery, cmd.gui.hintText.innerText);
            assert.ok(fs.deductions[target], cmd.gui.hintText.innerText);
            assert.equal(loads.length, 0, 'signature lookup must leave proof bodies deferred');
            assert.equal(JSON.stringify(fs.propositions), before);
            assert.equal(cmd.gui.actionInput.readOnly, false);
            results.push(parser.stringifyTight(fs.deductions[target].value));
            console.log(JSON.stringify({ name, kind, loadedBodies: loads.length, milliseconds: Math.round(performance.now() - started) }));
        }
        assert.ok(results.every(value => value === results[0]), 'all entry points must generate the same rule');
    }
});
