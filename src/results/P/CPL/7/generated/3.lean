

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply subset_antisymm
    · -- `closure (interior A) ⊆ closure A`
      exact closure_mono interior_subset
    · -- `closure A ⊆ closure (interior A)` comes from `P1`
      have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
      simpa [closure_closure] using h
  · intro hEq
    intro x hx
    -- since `x ∈ A ⊆ closure A = closure (interior A)`
    have : x ∈ closure A := subset_closure hx
    simpa [hEq] using this

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_int : x ∈ interior (closure (interior A)) := hA hxA
      -- build the required inclusion
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- `A ⊆ A ∪ B`
        have h0 : (A : Set X) ⊆ A ∪ B := by
          intro z hz
          exact Or.inl hz
        -- apply monotonicity of the operators
        have h1 : interior A ⊆ interior (A ∪ B) := interior_mono h0
        have h2 : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h1
        exact interior_mono h2
      exact hsubset hx_int
  | inr hxB =>
      -- `x` comes from `B`
      have hx_int : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- `B ⊆ A ∪ B`
        have h0 : (B : Set X) ⊆ A ∪ B := by
          intro z hz
          exact Or.inr hz
        have h1 : interior B ⊆ interior (A ∪ B) := interior_mono h0
        have h2 : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h1
        exact interior_mono h2
      exact hsubset hx_int