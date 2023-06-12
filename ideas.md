- Remember how many clauses does that literal cover
- Remember how many unassigned literals a clause has
- Take the literal that maxes out on both metrics 

- if decide fails (all are satisfied)
- check if trail.size() == variables --> satisfied

- implement backjumping through remembering the last conflict on a stack and check if that was the cause of the backtracking

- add counters to dpll
- check improvements of the model solution 0.0.1 and change template
- add different decision heuristics