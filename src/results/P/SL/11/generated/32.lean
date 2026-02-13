

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hne : A.Nonempty) : (interior A).Nonempty := by
  classical
  by_contra hInt
  -- If `interior A` is empty, rewrite it to `∅`.
  have hIntEq : interior A = (∅ : Set X) := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have : (interior A).Nonempty := ⟨x, hx⟩
    exact (hInt this).elim
  -- Pick an element of `A` and send it through the `P2` containment.
  rcases hne with ⟨x, hxA⟩
  have hxInner : x ∈ interior (closure (interior A)) := hP2 hxA
  -- The rewritten set is empty, giving a contradiction.
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEq] using hxInner
  exact (Set.not_mem_empty x) this