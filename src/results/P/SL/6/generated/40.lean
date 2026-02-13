

theorem P3_closure_iff_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ Topology.P2 (closure A) := by
  -- First, show that `P3` for `closure A` implies `P2` for `closure A`.
  have h₁ : Topology.P3 (closure (A : Set X)) → Topology.P2 (closure A) := by
    intro hP3
    -- `P3` for `closure A` gives that `closure A` is open.
    have hOpen : IsOpen (closure (A : Set X)) :=
      (Topology.P3_closure_iff_open_closure (A := A)).1 hP3
    -- On an open set, `P3` is equivalent to `P2`.
    exact
      (Topology.P3_iff_P2_of_isOpen (A := closure (A : Set X)) hOpen).1 hP3
  -- Conversely, `P2` always implies `P3`.
  have h₂ : Topology.P2 (closure A) → Topology.P3 (closure (A : Set X)) := by
    intro hP2
    exact Topology.P2_implies_P3 (A := closure (A : Set X)) hP2
  exact ⟨h₁, h₂⟩