

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro _hP3
    exact P2_of_open (A := A) hA
  · intro hP2
    exact P2_implies_P3 (A := A) hP2

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1_and_P3 (A := A) hP2
  · rintro ⟨hP1, hP3⟩
    exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3

theorem P1_of_subset_of_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} (h₁ : Topology.P2 A) (h₂ : A ⊆ B) (h₃ : B ⊆ closure A) : Topology.P1 B := by
  intro x hxB
  -- `x` is in `closure A`
  have hx_clA : x ∈ closure (A : Set X) := h₃ hxB
  -- We show `closure A ⊆ closure (interior B)`
  have h_clA_subset_clIntB : closure (A : Set X) ⊆ closure (interior B) := by
    calc
      closure (A : Set X)
          ⊆ closure (interior A) := by
            -- from `P2 A`, we have `A ⊆ interior (closure (interior A))`
            -- hence, taking closures,
            -- `closure A ⊆ closure (interior (closure (interior A))) = closure (interior A)`
            have hA_sub : (A : Set X) ⊆ interior (closure (interior A)) := h₁
            simpa [closure_closure] using closure_mono hA_sub
      _ ⊆ closure (interior B) := by
            -- since `A ⊆ B`, we have `interior A ⊆ interior B`
            have h_int : (interior A : Set X) ⊆ interior B := interior_mono h₂
            exact closure_mono h_int
  exact h_clA_subset_clIntB hx_clA

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A := by
  intro x hx
  -- In a subsingleton, any nonempty set is the whole universe.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Conclude the required membership.
  simpa [hA_univ, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A := by
  intro x hx
  -- Since `X` is a subsingleton, any nonempty set is the whole universe.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Conclude the required membership.
  simpa [hA_univ, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A := by
  intro x hx
  -- In a subsingleton, any nonempty set is the whole universe.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Conclude the required membership.
  simpa [hA_univ, closure_univ, interior_univ] using (Set.mem_univ x)