# LTL Model Checking Applied to a Puzzle Game

> TIPE (individual research project), French preparatory class (CPGE, MPI track)

This project implements **LTL model checking from scratch**: given a system (modeled as a Kripke structure) and a property written as a Linear Temporal Logic formula, it automatically decides whether the system satisfies the property — and if not, produces a concrete counter-example. As a test case, it solves the classic **wolf, goat and cabbage river-crossing puzzle**, showing that a puzzle traditionally solved by hand or by graph search can instead be solved by encoding it as a verification problem.

## The puzzle

A man must carry a wolf, a goat, and a cabbage across a river. The boat only carries the man plus maximum one item at a time. Left unsupervised, the wolf eats the goat, and the goat eats the cabbage. The question: is there a sequence of crossings that gets everyone across safely?    

This is normally solved with a short, graph search. The point of this project is different: instead of writing a search tailored to this one puzzle, the puzzle is encoded as a generic verification question — "**does there exist a path in this state graph along which this temporal property eventually holds?**" — and a general-purpose algorithm answers it, without knowing anything about wolves or boats.

## Background: LTL and model checking

**Model checking** is a formal verification technique: given a model of a system's possible behaviors and a specification of what it should (or shouldn't) do, an algorithm exhaustively checks whether every behavior satisfies the specification. It's widely used to verify hardware, protocols, and safety-critical software, where "testing a few cases" isn't good enough.

The system's behavior is modeled as a **Kripke structure**: states, transitions between them, and, in each state, which atomic propositions are true (e.g. `wolf_on_left`, `goat_on_right`).

The specification is written in **Linear Temporal Logic (LTL)** — propositional logic extended with operators over time, such as:
- `X φ`: φ holds at the *next* step
- `F φ`: φ holds *eventually*
- `G φ`: φ holds *always* (globally)
- `φ U ψ`: φ holds *until* ψ becomes true

For the puzzle, the property checked is roughly *"eventually, everyone is on the right bank"* — `F (all_on_right)`.

## Implementation idea

The classic way to check an LTL property (Vardi–Wolper's automata-theoretic approach) is to turn the problem into a **graph search for an infinite loop**, via the following pipeline:

1. **Formula → Büchi automaton.** The LTL formula is negated, converted to negation normal form, and expanded into a **generalized Büchi automaton**: an automaton over infinite words that accepts exactly the executions *violating* the property. This uses the tableau construction of Gerth, Peled, Vardi & Wolper.
2. **Simplification.** The generalized Büchi automaton (multiple accepting sets) is converted into a standard Büchi automaton (a single accepting set) via the standard counting construction, then determinized over the relevant propositions with a powerset construction.
3. **System → Büchi automaton.** The Kripke structure is itself translated into a Büchi automaton that accepts exactly its own executions.
4. **Product.** The two automata are combined into a single **product automaton**, whose accepted words are exactly the system's executions that violate the property.
5. **Emptiness check.** The system satisfies the property **if and only if this product automaton's language is empty** — i.e. no reachable accepting cycle ("lasso") exists. This reduces to a graph search: a DFS finds candidate accepting states, then a second search looks for a cycle through one of them. If a lasso is found, it *is* a counter-example: a concrete infinite execution violating the property, which — for the puzzle — reads as a valid solution.

## Project structure

- `model_checking.ml` / `.mli` — the full pipeline: formula parsing helpers, NNF, tableau construction, generalized Büchi automaton, powerset & simplification to a standard Büchi automaton, Kripke-to-automaton translation, product construction, and lasso search
- `debug.ml` / `.mli` — pretty-printing helpers for formulas, automata, and solutions
- `examples.ml` / `.mli` — the wolf/goat/cabbage puzzle, encoded three different ways (see Results)
- `main.ml` — entry point, runs the model checker on a chosen formula/system pair

## Build & run

```bash
dune build
dune exec ./main.exe
```

## Results

The puzzle has two rules:
1. **Safety**: nobody gets eaten (the wolf must never be left alone with the goat, nor the goat with the cabbage, without the man).
2. **Boat capacity**: the man can carry at most one item at a time.
Each rule can be enforced in two different places:
- **In the Kripke structure**: the illegal states are simply never added to the graph — the system itself cannot be in an unsafe configuration.
- **In the LTL formula**: all states exist in the graph, including unsafe ones, and the rule is instead stated as a temporal property that every execution must satisfy.
`examples.ml` tests three combinations, all checked against the same goal (*"eventually, everyone is on the right bank"*):
 
| Encoding | Safety rule | Boat capacity rule | Execution time | Boat trips |
|:---:|:---:|:---:|:---:|:---:|
| All in KS | Kripke structure | Kripke structure | 0.0001 s | 12 |
| Half and half | LTL formula | Kripke structure | 0.005 s | 12 |
| All in formula | LTL formula | LTL formula | 17.4 s | 20 |
 
The three encodings describe the exact same puzzle and all find a valid solution, but their **execution time differs by five orders of magnitude**. This is the central trade-off of this approach:
 
- Enforcing a rule **in the Kripke structure** means doing more work up front (checking the rule while building the graph), but the resulting graph stays small, since illegal states are never created in the first place.
- Enforcing a rule **in the formula** skips that up-front check, but the rule becomes an extra temporal subformula that the tableau construction has to track. Thus, all the automata become  bigger and complexity explodes.
For a puzzle this small, both choices still finish in reasonable time. But the "all in formula" column already shows the cost clearly: a 5-order-of-magnitude slowdown and a longer, less direct solution (20 trips instead of 12). On a larger system (more items, more states), this gap would only widen, since the automaton built from the formula grows independently of how large the underlying system is. Then, **deciding where a rule is enforced is a real design choice for using model checking effectively**.


## Why this matters beyond the puzzle

The wolf/goat/cabbage puzzle is a toy example, but the technique isn't: LTL model checking is used in practice to verify hardware and safety-critical software, and — closer to robotics — to specify and verify **temporal task planning** for autonomous systems (e.g. "the robot must eventually reach the goal, and must never enter the restricted zone while carrying the payload"). This project implements that same automata pipeline, from formula to counter-example, which is the core process behind those applications.

## References

Gerth, R., Peled, D., Vardi, M.Y., & Wolper, P. (1995). *Simple On-the-Fly Automatic Verification of Linear Temporal Logic*. PSTV.

Vardi, M.Y., & Wolper, P. (1986). *An Automata-Theoretic Approach to Automatic Program Verification*. LICS.
