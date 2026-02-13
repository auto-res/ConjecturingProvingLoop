

theorem P2_prod_iterated {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) : Topology.P2 (A := Set.prod (Set.prod A B) C) := by
  -- Step 1: obtain `P2` for `A × B` in the product space `X × Y`.
  have hAB : Topology.P2 (A := Set.prod A B) := by
    simpa using
      (Topology.P2_product
        (X := X) (Y := Y)
        (A := A) (B := B)
        (hA := hA) (hB := hB))
  -- Step 2: combine this with `C`, viewed in the space `Z`.
  simpa using
    (Topology.P2_product
      (X := X × Y) (Y := Z)
      (A := Set.prod A B) (B := C)
      (hA := hAB) (hB := hC))

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) : closure A ∪ closure B ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- 1. `closure A ⊆ closure (interior A)`
      have h₁ : (closure (A) : Set X) ⊆ closure (interior A) := by
        have hA_subset : (A : Set X) ⊆ closure (interior A) := hA
        have h_cl : closure (A : Set X) ⊆ closure (closure (interior A)) :=
          closure_mono hA_subset
        simpa [closure_closure] using h_cl
      -- 2. `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have h₂ : (closure (interior A) : Set X) ⊆
          closure (interior (A ∪ B)) := by
        have h_int : (interior A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact closure_mono h_int
      exact h₂ (h₁ hxA)
  | inr hxB =>
      -- 1. `closure B ⊆ closure (interior B)`
      have h₁ : (closure (B) : Set X) ⊆ closure (interior B) := by
        have hB_subset : (B : Set X) ⊆ closure (interior B) := hB
        have h_cl : closure (B : Set X) ⊆ closure (closure (interior B)) :=
          closure_mono hB_subset
        simpa [closure_closure] using h_cl
      -- 2. `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have h₂ : (closure (interior B) : Set X) ⊆
          closure (interior (A ∪ B)) := by
        have h_int : (interior B : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact closure_mono h_int
      exact h₂ (h₁ hxB)