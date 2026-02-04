# Erdős Problem 167 Formalization Log

## Problem Statement

If $G$ is a graph with at most $k$ edge disjoint triangles then can $G$ be made triangle-free after removing at most $2k$ edges?

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/167.lean`
- **Definition:** `AreEdgeDisjointTriangles` defines the property that a set of triangles (represented as `Finset V` of size 3) are edge-disjoint.
- **Conjecture:** `erdos_167` states Tuza's conjecture: if the maximum size of a set of edge-disjoint triangles is $k$, then there exists a set of at most $2k$ edges whose removal makes the graph triangle-free.

## Implementation Notes

- Used `SimpleGraph.IsNClique 3` to identify triangles.
- Used `SimpleGraph.deleteEdges` to represent the removal of edges.
- Used `SimpleGraph.CliqueFree 3` for the triangle-free condition.
- The condition "at most $k$ edge disjoint triangles" is formalized as: for all finsets $S$ of edge-disjoint triangles, $|S| \leq k$.

## Build Status

- Built with `lake build FormalConjectures/ErdosProblems/167.lean`.
