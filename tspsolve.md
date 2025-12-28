Skip to content
Chat history

You said:
what is the most common lp based solution for optimal tsp solving
ChatGPT said:
For exact (optimal) TSP solving, the most widely-used LP-based approach is:

👉 Branch-and-Cut built on the DFJ (subtour-elimination) LP formulation
Here’s what that means in practice:

Start with an LP relaxation of the TSP:

Use the Dantzig–Fulkerson–Johnson (DFJ) formulation.

Variables indicate whether each edge is in the tour.

Degree constraints ensure 2 edges meet at every city.

Subtour-elimination constraints (SECs) are initially omitted (too many to list explicitly).

Solve the LP, then:

If the solution has subtours, detect them and

add violated SECs as cutting planes (also add stronger families like comb, blossom, clique-tree inequalities, etc.).

Repeat until no violated cuts remain.

If the resulting LP solution is still fractional, apply branch-and-bound — giving:

➜ Branch-and-Cut
This is the strategy used by top TSP solvers such as Concorde. It’s the workhorse method that scales best for exact solutions.

Related notes
The Held–Karp bound (1-tree/Lagrangian relaxation) is often used to strengthen the LP and guide branching — but the core framework is still branch-and-cut.

The MTZ formulation (Miller–Tucker–Zemlin) is also LP-based but produces far weaker relaxations and is rarely used for large, optimal TSP solving.

TL;DR
Most common LP-based optimal TSP method:

DFJ subtour-elimination formulation + cutting planes + branch-and-bound = Branch-and-Cut.

If you’d like, I can sketch the DFJ LP, show how cuts are generated, or compare it with Held–Karp and MTZ.

You said:
can it be improved
ChatGPT said:
Short answer: yes — but only at the margins.
The branch-and-cut (DFJ + cutting planes) framework is already extremely mature, and most “improvements” today are refinements inside that framework rather than brand-new ideas.

Below is a practical map of where LP-based TSP solving has been improved — and where the limits are.

✅ Proven ways branch-and-cut has been improved
1️⃣ Much stronger cutting planes (polyhedral work)
Concorde’s success came largely from decades of discovering and implementing families of inequalities:

comb, 2-matching, blossom, clique-tree

path, domino-parity cuts

lifted subtour inequalities

problem-specific cuts (e.g., Euclidean TSP geometric cuts)

The improvements here continue — but they are incremental and highly technical.

2️⃣ Better separation algorithms
Finding violated cuts quickly is as important as the cuts themselves. Modern improvements include:

heuristic separation before exact separation

prioritizing “cheap but effective” cuts

dynamically learning which cuts pay off on a given instance

This reduces LP solve time and branch-and-bound depth.

3️⃣ Integration with strong relaxations
LP bounds can be strengthened by combining:

Held–Karp 1-tree / Lagrangian relaxation

dual ascent methods

sometimes even SDP or spectral bounds (costly but occasionally useful)

These can tighten the LP before branching.

4️⃣ Primal heuristics inside the LP search
While solving the LP tree, solvers inject good tours:

Lin–Kernighan (LK/LKH)

local improvement / patching heuristics

random restarts guided by LP solutions

Good incumbents massively shrink the search tree.

5️⃣ Cutting-plane management
Too many cuts can hurt. Modern solvers:

age and delete inactive cuts

avoid adding weak or redundant ones

reorder solves to preserve warm starts

This gives big practical wins.

6️⃣ Parallelization and engineering
Better numerical stability, caching, memory layouts, and parallel separation/LP solves all matter in practice.

🚧 Alternatives that sound better but rarely beat branch-and-cut
❌ MTZ (Miller–Tucker–Zemlin)
Easy to write but weak bounds → scales poorly.

⚠️ Branch-and-price / column generation
Useful for routing problems with side constraints (VRP, time windows),
but for pure TSP, edge-based DFJ + cuts remains stronger.

⚠️ SDP relaxations
Beautiful theory, but solving SDPs is too expensive at scale.

⚠️ “Neural” or metaheuristic-driven exact solvers
Great heuristics, but they rarely improve optimal LP search.

📌 The realistic conclusion
LP-based optimal TSP solving can still be improved — but mostly through smarter cuts, separation heuristics, and engineering.

Breakthroughs tend to be subtle polyhedral insights, not entirely new frameworks.

Concorde (and successors like ongoing research solvers) are still essentially DFJ + very advanced branch-and-cut, and they remain state-of-the-art.

If you’re curious, I can go deeper into any of these:
show the DFJ LP and where each improvement plugs in

compare Held–Karp vs DFJ numerically

sketch a simple branch-and-cut implementation

discuss why MTZ is weak

look at specific research directions still open

Just tell me!

No file chosenNo file chosen
ChatGPT can make mistakes. Check important info. See Cookie Preferences.
