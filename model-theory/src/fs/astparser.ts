import { AST } from "./astmgr.js"
import { TR } from "../lang.js";
export class ASTParser {
    constructor(private readonly templateSyntax = false) { }
    keywords = ["E!", "⊢M", "<>", "Union", "{}", "Equiv", "<=", ">=", "/|"];
    symChar = "VEMUIX()@~^<>|&=,;:[]!⊢+-*/{}\\";
    ast: AST;
    cursor: number = 0;
    tokens: string[];
    token: string;
    stringifyTight(ast: AST, bracket: boolean = false): string {
        const nd = ast.nodes;
        if (ast.type === "fn" || ast.type === "predtemplate") {
            if (ast.name === "{") return `{${nd.map(n => this.stringifyTight(n)).join(",")}}`;
            return `${ast.name === "(" ? "" : ast.name}(${nd.map(n => this.stringifyTight(n)).join(",")})`;
        }
        if (["replvar", "rule", "predref", "arglist"].includes(ast.type)) {
            return ast.name;
        }
        if (ast.type === "meta") {
            const c = `${nd[0].nodes.map(n => this.stringifyTight(n, ast.name === "⊢M")).join(",")}${ast.name}${nd[1].nodes.map(n => this.stringifyTight(n, ast.name === "⊢M")).join(",")}`;
            return bracket ? `(${c})` : c
        }
        switch (ast.name) {
            case "~": case "!": return `${ast.name}${this.stringifyTight(nd[0], true)}`;
            case "V": case "E": case "E!": return `(${ast.name}${this.stringifyTight(nd[0])}:${this.stringifyTight(nd[1], true)})`;
            case "{|": return `{${this.stringifyTight(nd[0])}@${this.stringifyTight(nd[1])}|${this.stringifyTight(nd[2], true)}}`;
            case "|}": return `{${this.stringifyTight(nd[2], true)}|${this.stringifyTight(nd[0])}@${this.stringifyTight(nd[1])}}`;
            default:
                const sym = ast.name;
                const c = `${this.stringifyTight(nd[0], true)}${sym}${this.stringifyTight(nd[1], true)}`;
                return bracket ? `(${c})` : c
        }
    }
    stringify(ast: AST): string {
        const nd = ast.nodes;
        if (ast.type === "fn" || ast.type === "predtemplate") {
            if (ast.name === "{") return `{${nd.map(n => this.stringify(n)).join(", ")}}`;
            return `${ast.name === "(" ? "" : ast.name}(${nd.map(n => this.stringify(n)).join(", ")})`;
        }
        if (["replvar", "rule", "predref", "arglist"].includes(ast.type)) {
            return ast.name;
        }
        if (ast.type === "meta") {
            return `(${nd[0].nodes.map(n => this.stringify(n)).join(", ")} ${ast.name} ${nd[1].nodes.map(n => this.stringify(n)).join(", ")})`;
        }
        switch (ast.name) {
            case "~": case "!": return `${ast.name}${this.stringify(nd[0])}`;
            case "V": case "E": case "E!": return `(${ast.name}${this.stringify(nd[0])}: ${this.stringify(nd[1])})`;
            case "{|": return `{${this.stringify(nd[0])}@${this.stringify(nd[1])} | ${this.stringify(nd[2])}}`;
            case "|}": return `{${this.stringify(nd[2])} | ${this.stringify(nd[0])}@${this.stringify(nd[1])}}`;
            default:
                return `(${this.stringify(nd[0])} ${ast.name} ${this.stringify(nd[1])})`;
        }
    }
    parse(s: string, strict = false) {
        this.cursor = 0;
        this.tokenise(s.replaceAll("∀", "V").replaceAll("∃", "E").replaceAll("∈", "@").replaceAll("¬", "~")
            .replaceAll("→", ">").replaceAll("↔", "<>").replaceAll("⊂", "<").replaceAll("∪", "U").replaceAll("∩", "I")
            .replaceAll("∧", "&").replaceAll("∨", "|").replaceAll("ω", "omega").replaceAll("≤", "<=").replaceAll("≥", ">=").replaceAll("∣", "/|")
            .replaceAll("ℕ", "N").replaceAll("ℤ", "Z").replaceAll("ℚ", "Q").replaceAll("ℝ", "R").replaceAll("×","*")
        );
        this.nextSym();
        const ast = this.meta();
        // Model expressions must never silently accept a parsed prefix.
        if ((strict || this.templateSyntax || /#(?:sat|abs|abst|absf)\s*\(/.test(s)) && this.token !== undefined) throw new Error("表达式末尾有未解析内容：" + this.token);
        return ast;
    }
    stringifySaved(ast: AST): string {
        const templates = (a: AST): boolean => ["predtemplate", "predref", "arglist"].includes(a.type) || !!a.nodes?.some(templates);
        // This prefix cannot begin a valid legacy expression. It versions only
        // the expression's syntax, not models, signatures or template bindings.
        return templates(ast) ? "@model-v1:" + JSON.stringify(ast) : this.stringifyTight(ast);
    }
    parseSaved(source: string): AST {
        if (!source.startsWith("@model-v1:")) return new ASTParser(false).parse(source);
        let budget = 16384;
        const read = (a: any): AST => {
            if (--budget < 0 || !a || typeof a.name !== "string" ||
                !["fn", "sym", "meta", "rule", "replvar", "predtemplate", "predref", "arglist"].includes(a.type) ||
                (a.nodes !== undefined && !Array.isArray(a.nodes))) throw new Error("模板表达式的存档结构无效");
            const result: AST = { type: a.type, name: a.name };
            if (a.nodes) result.nodes = a.nodes.map(read);
            return result;
        };
        // Preserve legacy literal double-quote names even in an expression that
        // also contains new templates. No predicate definition data is stored.
        return read(JSON.parse(source.slice(10)));
    }
    private tokenise(s: string) {
        for (let i = 0; i < this.keywords.length; i++) {
            s = s.replaceAll(this.keywords[i], " #keyword" + i + " ");
        }
        let word = "";
        const arr: string[] = [];
        for (let i = 0; i < s.length; i++) {
            const c = s[i];
            if (this.symChar.includes(c)) {
                if (word !== "") {
                    arr.push(word); word = "";
                }
                arr.push(c);
                continue;
            }
            if (c === " ") {
                if (word !== "") {
                    arr.push(word); word = "";
                }
                continue;
            }
            word += c;
        }
        if (word !== "") {
            arr.push(word);
        }
        this.tokens = arr.map(token => token.startsWith("#keyword") ? this.keywords[token.slice(8)] : token);
    }
    private prevToken(index: number) {
        return this.tokens[this.cursor - index - 1];
    }
    private nextSym() {
        this.token = this.tokens[this.cursor++];
    }
    private moveCursor(cursor: number) {
        this.cursor = cursor;
        this.token = this.tokens[this.cursor - 1];
    }
    private acceptVar() {
        if (!this.symChar.includes(this.token) || this.token.length > 1) {
            if (!this.token) return false; //eof
            this.nextSym();
            return true;
        }
        return false;
    }
    private expectVar() {
        if (this.acceptVar()) return true;
        throw TR(`语法错误：未找到变量`);
    }
    private acceptSym(s: string) {
        if (s === this.token) {
            this.nextSym();
            return true;
        }
        return false;
    }
    private expectSym(s: string) {
        if (this.acceptSym(s)) return true;
        throw TR(`语法错误：未找到符号`) + `"${s}"`;
    }


    private itemTerm(): AST {

        if (this.acceptVar()) {
            const word = this.prevToken(1);
            const predicate = this.templateSyntax && /^"[a-z_][a-z0-9_]*$/.test(word);
            const list = this.templateSyntax && /^\.\.\.\$[a-z_][a-z0-9_]*$/.test(word);
            if (this.templateSyntax && word.startsWith("...$") && !list) throw new Error("参数列表名称必须为 ...$ 加小写字母、数字或下划线");
            if (this.templateSyntax && word.startsWith('"') && !predicate) throw new Error("谓词模板名称必须是双引号前缀加小写字母、数字或下划线");
            if (this.acceptSym("(")) {
                const fnName = this.prevToken(2);
                if (list) throw new Error("参数列表模板不能作为函数调用");
                if (this.acceptSym(")")) return { type: predicate ? "predtemplate" : "fn", name: fnName, nodes: [] };
                const nodes = [this.meta()];
                while (this.token === ",") {
                    this.nextSym();
                    nodes.push(this.meta());
                }
                this.expectSym(")");
                return { type: predicate ? "predtemplate" : "fn", name: fnName, nodes };
            } else {
                return { type: predicate ? "predref" : list ? "arglist" : "replvar", name: word };
            }
        } else if (this.acceptSym("(")) {
            if (this.acceptSym(")")) return { type: "fn", name: "(", nodes: [] };
            const nodes = [this.meta()];
            while (this.token === ",") {
                this.nextSym();
                nodes.push(this.meta());
            }
            this.expectSym(")");
            if (nodes.length === 1) {
                return nodes[0];
            }
            return { type: "fn", name: "(", nodes };
        } else if (this.acceptSym("{")) {
            const c = this.cursor;
            const t = this.token;
            this.cursor = c;
            this.token = t;
            const nodes = [this.meta()];
            while (this.token === ",") {
                this.nextSym();
                nodes.push(this.meta());
            }
            this.expectSym("}");
            // {xx|xx}
            if (nodes.length === 1 && nodes[0].type === "sym" && nodes[0].name === "|") {
                // {x@x|xx}
                const sub1 = nodes[0].nodes[0];
                if (sub1.name === "@" && sub1.type === "sym") {
                    return {
                        type: "sym", name: "{|", nodes: [
                            ...sub1.nodes, nodes[0].nodes[1]
                        ]
                    };
                }

                // {xx|x@x}
                const sub2 = nodes[0].nodes[1];
                if (sub2.name === "@" && sub2.type === "sym") {
                    return {
                        type: "sym", name: "|}", nodes: [
                            ...sub2.nodes, nodes[0].nodes[0]
                        ]
                    };
                }
            }
            return { type: "fn", name: "{", nodes };
        } else if (this.acceptSym("-")) {
            // -n in Z
            if (this.acceptVar()) return { type: "replvar", name: "-" + this.prevToken(1) };
            throw TR("语法错误");
        } else if (this.acceptSym("+")) {
            // +n in Z
            if (this.acceptVar()) return { type: "replvar", name: "+" + this.prevToken(1) };
            throw TR("语法错误");
        } else {
            throw TR("语法错误");
        }
    }
    private boolTerm6(): AST {
        let val = this.itemTerm();
        while (this.token === "X" || this.token === "*" || this.token === "/" || this.token === "I" || this.token?.match(/^\$\$.+/)) {
            const name = this.token;
            this.nextSym();
            let val2 = this.itemTerm();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    private boolTerm5(): AST {
        let val = this.boolTerm6();
        while (this.token === "+" || this.token === "U" || this.token === "\\" || this.token === "-") {
            const name = this.token;
            this.nextSym();
            let val2 = this.boolTerm6();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    private boolTerm4(): AST {
        let val = this.boolTerm5();
        while (this.token === "@" || this.token === "=" || this.token === "<" || this.token === "<=" || this.token === ">=" || this.token === "/|" || this.token?.match(/^\$\$.+/)) {
            const name = this.token;
            this.nextSym();
            let val2 = this.boolTerm5();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    private boundedVar(): AST {
        if (this.token.match(/^#?#v*nf$/)) {
            this.nextSym();
            this.expectSym("(");
            const fnName = this.prevToken(2);
            const nodes = [this.meta()];
            while (this.token === ",") {
                this.nextSym();
                nodes.push(this.meta());
            }
            this.expectSym(")");
            return { type: "fn", name: fnName, nodes };
        } else {
            this.expectVar();
            return { type: "replvar", name: this.prevToken(1) };
        }
    }
    private boolTerm3(): AST {
        if (this.token === "V" || this.token === "E" || this.token === "E!") {
            const name = this.token;
            this.nextSym();
            // this.expectVar();
            return {
                type: "sym", name,
                nodes: [
                    this.boundedVar(),
                    (this.acceptSym(":"), this.boolTerm3()) // ":" is optional
                ]
            };
        } else if (this.token === "~") {
            this.nextSym();
            return { type: "sym", name: "~", nodes: [this.boolTerm3()] };
        } else if (this.token === "!") {
            this.nextSym();
            return { type: "sym", name: "!", nodes: [this.boolTerm3()] };
        } else {
            return this.boolTerm4();
        }
    }
    private boolTerm2(): AST {
        let val = this.boolTerm3();
        while (this.token === "&" || this.token === "^") {
            const name = this.token;
            this.nextSym();
            let val2 = this.boolTerm3();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    private boolTerm1(): AST {
        let val = this.boolTerm2();
        while (this.token === "|") {
            this.nextSym();
            let val2 = this.boolTerm2();
            val = { type: "sym", name: "|", nodes: [val, val2] };
        }
        return val;
    }
    private bool(): AST {
        let val = this.boolTerm1();
        if (this.token === ">" || this.token === "<>") {
            const name = this.token;
            this.nextSym();
            let val2 = this.bool();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    private meta(): AST {
        let conditions = [];
        let rollBackCursor: number;
        if (this.token !== "⊢M" && this.token !== "⊢" && this.token !== "⊧") {
            // parse meta-condition
            conditions.push(this.bool());
            rollBackCursor = this.cursor;
            while (this.token === ",") {
                this.nextSym();
                conditions.push(this.bool());
            }
        }
        const sym = this.token;
        if (this.token !== "⊢M" && this.token !== "⊢" && this.token !== "⊧") {
            this.moveCursor(rollBackCursor); // rollback to first ","
            return conditions[0]; // not meta, just bool
        }
        this.nextSym();
        let conclusions = [];
        conclusions.push(this.meta());
        while (this.token as string === ",") {
            this.nextSym();
            conclusions.push(this.meta());
        }
        return {
            type: "meta", name: sym, nodes: [
                { type: "fn", name: "#array", nodes: conditions },
                { type: "fn", name: "#array", nodes: conclusions },
            ]
        };
    }
}
