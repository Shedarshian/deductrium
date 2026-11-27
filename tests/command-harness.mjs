// Minimal rendering adapter for exercising the real command and lookup code
// in Node. No browser, storage, game save, or command implementation is replaced.
import { FSCmd } from '../js/fs/cmd.js';
import { FSGui } from '../js/fs/gui.js';
import { ASTParser } from '../js/fs/astparser.js';

class TextElement {
    children = [];
    text = '';
    className = '';
    get innerText() { return this.text + this.children.map(child => child.innerText ?? '').join(''); }
    set innerText(value) { this.text = String(value); this.children = []; }
    get innerHTML() { return this.innerText; }
    set innerHTML(value) { this.innerText = value; }
    appendChild(child) { this.children.push(child); return child; }
}

export async function withCommandDom(action) {
    const previous = globalThis.document;
    globalThis.document = { createElement: () => new TextElement(), querySelector: () => null, querySelectorAll: () => [] };
    try { return await action(); }
    finally {
        if (previous === undefined) delete globalThis.document;
        else globalThis.document = previous;
    }
}

export function ruleCommand(fs, buffer) {
    const cmd = Object.create(FSCmd.prototype);
    Object.assign(cmd, { cmdBuffer: buffer, escClear: true, pListMasked: false, astparser: new ASTParser(), lastDeduction: null });
    const gui = Object.create(FSGui.prototype);
    Object.assign(gui, {
        formalSystem: fs, cmd, isMobile: true, unlockedMacro: true, cmdBtns: [],
        deductions: Object.keys(fs.deductions), metarules: Object.keys(fs.metaRules),
        actionInput: { readOnly: false, value: '' }, hintText: new TextElement(),
        updatePropositionList() {}, clearPListMasked() {},
        addToDeductions(name) { if (!this.deductions.includes(name)) this.deductions.push(name); },
        addSpan(parent, text) { const node = new TextElement(); node.innerText = text; parent.appendChild(node); return node; },
        tree2HTML(tree) { const node = new TextElement(); node.innerText = JSON.stringify(tree); return node; },
        ast2HTML(_, ast) { const node = new TextElement(); node.innerText = cmd.astparser.stringify(ast); return node; }
    });
    cmd.gui = gui;
    return cmd;
}
