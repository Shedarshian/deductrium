export type AST = { type: string, name: string, nodes?: AST[] };
export type ReplvarMatchTable = { [varname: string]: AST };

export class ASTMgr {
    clone(ast: AST): AST {
        const newast: AST = {
            type: ast.type, name: ast.name
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p));
        }
        return newast;
    }
    assign(ast: AST, value: AST) {
        const v = this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
    }
    equal(ast1: AST, ast2: AST) {
        if (ast1 === ast2) return true;
        if (ast1.name !== ast2.name) return false;
        if (ast1.type !== ast2.type) return false;
        if (ast1.nodes?.length !== ast2.nodes?.length) return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.equal(ast1.nodes[i], ast2.nodes[i])) return false;
            }
        }
        return true;
    }
    // get all replvars, replNames is a given set to be added in
    getVarNames(ast: AST, varNames: Set<string>, reg: RegExp): Set<string> {
        if (ast.type === "replvar" && (reg ? ast.name.match(reg) : true)) varNames.add(ast.name);
        if (ast.nodes) for (const n of ast.nodes) {
            this.getVarNames(n, varNames, reg).forEach(v => varNames.add(v));
        }
        return varNames;
    }
    // replaceVarNamesInAst(ast: AST, filterReg: RegExp, replaceSrc: RegExp, replaceDst: string) {
    //     if (ast.type === "replvar" && ast.name.match(filterReg)) {
    //         ast.name = ast.name.replace(replaceSrc, replaceDst);
    //     }
    //     if (ast.nodes?.length) {
    //         for (const n of ast.nodes) {
    //             this.replaceVarNamesInAst(n, filterReg, replaceSrc, replaceDst);
    //         }
    //     }
    // }
    // exact replace, without matching $.*s
    // nth: null or -1 for replaceAll, others for replace nth(start from 0) 
    replace(ast: AST, searchValue: AST, replaceValue: AST, preventCircularReplace?: boolean, nth?: number, matchedTimes: number = 0) {
        nth ??= -1;
        if (this.equal(ast, searchValue)) {
            if (nth === -1 || (nth === matchedTimes)) {
                this.assign(ast, replaceValue);
                if (preventCircularReplace) { ast.type = "$" + ast.type; }
            }
            return matchedTimes+1;
        }
        if (ast.nodes?.length && !ast.type.startsWith("$")) {
            for (const n of ast.nodes) {
                matchedTimes = this.replace(n, searchValue, replaceValue, preventCircularReplace, nth, matchedTimes);
            }
        }
        return matchedTimes;
    }
    finishReplace(ast: AST) {
        if (ast.type.startsWith("$")) ast.type = ast.type.slice(1);
        if (ast.nodes?.length) {
            for (const n of ast.nodes) this.finishReplace(n);
        }
    }
    replaceByMatchTable(ast: AST, matchResult: ReplvarMatchTable) {
        for (const [varname, matchedAst] of Object.entries(matchResult)) {
            if (matchedAst.type === "predicatebinding" || matchedAst.type === "argbinding") continue;
            this.replace(ast, { type: "replvar", name: varname }, matchedAst, true);
        }
        this.finishReplace(ast);
        const instantiate = (a: AST) => {
            // Values inserted from a caller are traversed once; never recursively
            // reinterpret a bound predicate name as a new template.
            if (a.type === "predref") {
                const binding = matchResult[a.name];
                if (!binding) return;
                if (binding.type !== "predicatebinding" || binding.nodes[0].name !== "1") throw new Error("论域模板必须绑定一元谓词");
                this.assign(a, { type: "replvar", name: binding.name }); return;
            }
            if (a.type === "predtemplate") {
                const expanded: AST[] = [];
                for (const [i, n] of a.nodes.entries()) {
                    if (n.type === "arglist") {
                        if (i !== a.nodes.length - 1) throw new Error("参数列表模板只能位于末尾");
                        const binding = matchResult[n.name];
                        if (binding) {
                            if (binding.type !== "argbinding") throw new Error("参数列表绑定类别错误");
                            expanded.push(...binding.nodes.map(v => this.clone(v)));
                        } else expanded.push(this.clone(n));
                    } else { instantiate(n); expanded.push(n); }
                }
                a.nodes = expanded;
                const binding = matchResult[a.name];
                if (binding) {
                    if (binding.type !== "predicatebinding" || expanded.some(n => n.type === "arglist") || expanded.length !== Number(binding.nodes[0].name)) throw new Error("谓词绑定与实际参数列表的元数不符");
                    a.type = "fn"; a.name = binding.name;
                }
                return;
            }
            if (a.type === "arglist") throw new Error("参数列表模板不能出现在普通项或公式位置");
            a.nodes?.forEach(instantiate);
        };
        instantiate(ast);
    }

}
