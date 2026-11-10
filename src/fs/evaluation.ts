/** One budget is shared by nested rule generation, matching and proof expansion. */
export type EvaluationLimits = {
    operations: number;
    astNodes: number;
    milliseconds: number;
    depth: number;
};

export const defaultEvaluationLimits: EvaluationLimits = {
    operations: 50_000, astNodes: 2_000_000, milliseconds: 3000, depth: 128
};

export class EvaluationBudget {
    private operations = 0;
    private astNodes = 0;
    private deadline: number;
    private depth = 0;
    constructor(readonly limits: EvaluationLimits) {
        this.deadline = performance.now() + limits.milliseconds;
    }
    check(nodes = 0) {
        this.astNodes += nodes;
        if ((!nodes && ++this.operations > this.limits.operations) || this.astNodes > this.limits.astNodes || performance.now() > this.deadline) {
            throw new Error("证明求值超过预算，请分层展开或减少本次操作的规模。 / Proof evaluation budget exceeded; expand one level at a time.");
        }
    }
    enter() {
        this.check();
        if (++this.depth > this.limits.depth) {
            this.depth--;
            throw new Error("证明依赖过深，请分层展开。 / Proof dependency depth exceeded.");
        }
    }
    leave() { this.depth--; }
}

// Evaluation is synchronous. Restore the previous budget when another system is
// called from inside an evaluation, rather than leaking state between systems.
export let activeBudget: EvaluationBudget | undefined;
export function withBudget<T>(budget: EvaluationBudget, action: () => T): T {
    const previous = activeBudget;
    activeBudget = budget;
    try { return action(); } finally { activeBudget = previous; }
}
