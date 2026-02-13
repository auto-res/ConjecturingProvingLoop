

theorem P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) : Topology.P1 (closure A) := by
  dsimp [Topology.P1] at h ⊢
  -- Step 1: `closure (interior A)` is contained in the target closure.
  have h2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Step 2: Combine with `h` to obtain a subset relation for `A`.
  have hcomb : (A : Set X) ⊆ closure (interior (closure A)) := h.trans h2
  -- Step 3: Take closures to upgrade the subset relation from `A` to `closure A`.
  have hfinal : closure A ⊆ closure (interior (closure A)) := by
    have : closure A ⊆ closure (closure (interior (closure A))) := closure_mono hcomb
    simpa [closure_closure] using this
  exact hfinal