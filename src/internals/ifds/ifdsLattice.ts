/**
 * Lattice implementation for IFDS analysis.
 * The IFDS lattice operates on sets of dataflow facts.
 */

import { JoinSemilattice } from "../lattice";
import { DataflowFact, PathContext } from "./ifds";

/**
 * A lattice implementation for IFDS that operates on sets of dataflow facts.
 *
 * This is a join semilattice where:
 * - The bottom element is the empty set
 * - Join is set union
 * - Ordering is subset relationship (a ≤ b iff a ⊆ b)
 */
export class IFDSLattice implements JoinSemilattice<Set<DataflowFact>> {
  /**
   * Returns the bottom element of the lattice: the empty set.
   */
  bottom(): Set<DataflowFact> {
    return new Set();
  }

  /**
   * Joins two sets of dataflow facts using set union.
   */
  join(a: Set<DataflowFact>, b: Set<DataflowFact>): Set<DataflowFact> {
    const result = new Set<DataflowFact>();

    // Add all facts from set a
    for (const fact of a) {
      result.add(fact);
    }

    // Add all facts from set b, merging path contexts for duplicate facts
    for (const bFact of b) {
      // Check if this fact already exists in the result (by id and node)
      const existingFact = this.findMatchingFact(result, bFact);

      if (existingFact) {
        // Found a matching fact - merge path contexts if they exist
        if (existingFact.context || bFact.context) {
          const mergedContext = this.mergeContexts(
            existingFact.context,
            bFact.context,
          );
          // If contexts are different, update the existing fact
          if (!this.contextsEqual(existingFact.context, mergedContext)) {
            // Remove the existing fact
            result.delete(existingFact);
            // Add a new fact with the merged context
            result.add({
              ...existingFact,
              context: mergedContext,
            });
          }
        }
      } else {
        // No matching fact found, just add it
        result.add(bFact);
      }
    }
    return result;
  }

  /**
   * Checks if one set is a subset of another (a ≤ b iff a ⊆ b).
   */
  leq(a: Set<DataflowFact>, b: Set<DataflowFact>): boolean {
    if (a.size > b.size) return false;
    // Check if every fact in a has a matching fact in b
    for (const aFact of a) {
      const matchingFact = this.findMatchingFact(b, aFact);

      if (!matchingFact) {
        return false; // Fact in a not found in b
      }
      // If path contexts exist, check if a's context is more restrictive than b's
      if (aFact.context && matchingFact.context) {
        if (!this.contextIsSubsetOf(aFact.context, matchingFact.context)) {
          return false;
        }
      } else if (aFact.context && !matchingFact.context) {
        // a has a context but b doesn't - a is more specific, not a subset
        return false;
      }
    }
    return true;
  }

  /**
   * Finds a fact in a set that matches the given fact (same id and node).
   */
  private findMatchingFact(
    facts: Set<DataflowFact>,
    fact: DataflowFact,
  ): DataflowFact | undefined {
    for (const f of facts) {
      if (f.id === fact.id && f.node === fact.node) {
        return f;
      }
    }
    return undefined;
  }

  /**
   * Merges two path contexts.
   */
  private mergeContexts(
    ctx1: PathContext | undefined,
    ctx2: PathContext | undefined,
  ): PathContext | undefined {
    if (!ctx1) return ctx2;
    if (!ctx2) return ctx1;

    const result = new Map<number, boolean>();

    // Copy all conditions from ctx1
    for (const [condId, value] of ctx1.conditions) {
      result.set(condId, value);
    }

    // Merge with ctx2, handling conflicts
    for (const [condId, value] of ctx2.conditions) {
      if (result.has(condId)) {
        const existingValue = result.get(condId);
        if (existingValue !== value) {
          // Conflict - remove this condition (it's undetermined)
          result.delete(condId);
        }
      } else {
        result.set(condId, value);
      }
    }
    return { conditions: result };
  }

  /**
   * Checks if two path contexts are equal.
   */
  private contextsEqual(
    ctx1: PathContext | undefined,
    ctx2: PathContext | undefined,
  ): boolean {
    if (!ctx1 && !ctx2) return true;
    if (!ctx1 || !ctx2) return false;

    if (ctx1.conditions.size !== ctx2.conditions.size) return false;

    for (const [condId, value] of ctx1.conditions) {
      if (
        !ctx2.conditions.has(condId) ||
        ctx2.conditions.get(condId) !== value
      ) {
        return false;
      }
    }

    return true;
  }

  /**
   * Checks if one context is a subset of another.
   * A context is a subset of another if all its conditions are in the other
   * context with the same values.
   */
  private contextIsSubsetOf(ctx1: PathContext, ctx2: PathContext): boolean {
    for (const [condId, value] of ctx1.conditions) {
      if (
        !ctx2.conditions.has(condId) ||
        ctx2.conditions.get(condId) !== value
      ) {
        return false;
      }
    }

    return true;
  }
}
