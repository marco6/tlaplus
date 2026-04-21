package tlc2.tool.impl.jit;

/**
 * Compile-time reference to a JVM local variable slot allocated for a bound
 * variable (e.g., the quantified variable in a bounded-exists expression).
 * <p>
 * Instances are stored in the compilation {@link tlc2.util.Context} so that
 * variable lookups inside a quantifier body emit a direct {@code ALOAD} instead
 * of a context-chain lookup or an interpreter fallback.
 */
final class LocalRef {
    /** JVM local variable slot index. */
    final int localIndex;
    /** Kind of value stored in the local (always {@link ResultKind#Value} for TLA+ values). */
    final ResultKind kind;

    LocalRef(int localIndex, ResultKind kind) {
        this.localIndex = localIndex;
        this.kind = kind;
    }
}
