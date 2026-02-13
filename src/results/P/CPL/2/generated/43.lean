

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 (X:=X) A) : Topology.P1 (X:=X) (closure A) := by
  -- Unfold the definition of `P1`
  unfold Topology.P1 at h ⊢
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)`
  have h₁ : (closure (A : Set X)) ⊆ closure (interior A) := by
    -- take closures on both sides of `h`
    have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono h
    simpa [closure_closure] using this
  have hx₁ : x ∈ closure (interior A) := h₁ hx
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    have : (interior A : Set X) ⊆ interior (closure A) := by
      apply interior_mono
      exact subset_closure
    exact this
  -- Combine the two inclusions
  exact h₂ hx₁

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 (X:=X) A) : Topology.P1 (X:=X×Y) (A ×ˢ (Set.univ : Set Y)) := by
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hA (P1_univ (X := Y)))

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P3 (X:=X) A) : Topology.P3 (X:=X×Y) (A ×ˢ (Set.univ : Set Y)) := by
  simpa using
    (P3_prod (A := A) (B := (Set.univ : Set Y)) hA (P3_univ (X := Y)))