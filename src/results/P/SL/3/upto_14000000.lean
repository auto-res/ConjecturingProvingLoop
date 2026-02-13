

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro h
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset (s := closure (interior A))
  exact Set.Subset.trans h h₁

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hA
  have h₁ : interior (closure (interior (A : Set X))) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono (interior_subset (s := A))
  exact Set.Subset.trans hA h₁

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hA
  exact ⟨P2_implies_P1 hA, P2_implies_P3 hA⟩

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (A : Set X)) := by
  dsimp [Topology.P2]
  have h : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  simpa [interior_interior] using h

theorem P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx
  have h : (x : X) ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using h

theorem P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (A : Set X)) := by
  dsimp [Topology.P3]
  apply interior_maximal
  · exact subset_closure
  · exact isOpen_interior

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  have h : A ⊆ interior (closure A) := by
    apply interior_maximal
    · exact subset_closure
    · exact hA
  simpa [hA.interior_eq] using h

theorem P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  apply interior_maximal
  · exact subset_closure
  · exact hA

theorem P2_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior A))) := by
  have h : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using (P2_of_isOpen (A := interior (closure (interior A))) h)

theorem P3_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior A))) := by
  have h : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using (Topology.P3_of_isOpen (A := interior (closure (interior A))) h)

theorem P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _; exact Topology.P2_of_isOpen (A := A) hA
  · intro h; exact Topology.P2_implies_P1 (A := A) h

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) := by
  dsimp [Topology.P1]
  intro x hx
  have h : (x : X) ∈ closure (interior (closure A)) := subset_closure hx
  simpa [interior_interior] using h

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → closure (A : Set X) = closure (interior (A : Set X)) := by
  intro hA
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior A)`
    have h : closure (A : Set X) ⊆ closure (interior A) := by
      apply closure_minimal hA
      exact isClosed_closure
    exact h
  · -- `closure (interior A) ⊆ closure A`
    have h : closure (interior (A : Set X)) ⊆ closure A := by
      exact closure_mono (interior_subset (s := A))
    exact h

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → closure (A : Set X) = closure (interior (A : Set X)) := by
  intro hA
  have hP1 : Topology.P1 (A : Set X) := Topology.P2_implies_P1 (A := A) hA
  exact closure_eq_closure_interior_of_P1 (A := A) hP1

theorem Topology.P3_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro hP3
    dsimp [Topology.P3, Topology.P2] at hP3 ⊢
    intro x hx
    have : (x : X) ∈ interior (closure A) := hP3 hx
    simpa [hA.interior_eq] using this
  · intro hP2
    exact Topology.P2_implies_P3 (A := A) hP2

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P3 A ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  simpa using h₁.trans h₂.symm

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (A : Set X))) := by
  have h : IsOpen (interior (closure A)) := isOpen_interior
  simpa using (Topology.P3_of_isOpen (A := interior (closure A)) h)

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (A : Set X))) := by
  have h : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa using (Topology.P2_of_isOpen (A := interior (closure (A : Set X))) h)

theorem P1_interior_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P2 (interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen (A := interior (A : Set X)) hOpen)

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A : Set X)) (hB : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : (x : X) ∈ interior (closure (interior A)) := hA hAx
      have h_subset : interior (closure (interior A))
          ⊆ interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior A)
            ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact h_int
        exact interior_mono h_closure
      exact h_subset hxA
  | inr hBx =>
      have hxB : (x : X) ∈ interior (closure (interior B)) := hB hBx
      have h_subset : interior (closure (interior B))
          ⊆ interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior B)
            ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact h_int
        exact interior_mono h_closure
      exact h_subset hxB

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (A : Set X)) (hB : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : (x : X) ∈ interior (closure A) := hA hAx
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure (A : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hxA
  | inr hBx =>
      have hxB : (x : X) ∈ interior (closure B) := hB hBx
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure (B : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hxB

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A : Set X)) (hB : Topology.P1 (B : Set X)) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : (x : X) ∈ closure (interior A) := hA hAx
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hxA
  | inr hBx =>
      have hxB : (x : X) ∈ closure (interior B) := hB hBx
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hxB

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ⊆ interior (closure (A : Set X)) := by
  simpa using
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x _
  simp [interior_univ, closure_univ]

theorem closure_eq_closure_interior_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) →
      closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  intro hA
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior (closure A))`
    have h₁ : (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
      have hA' : (A : Set X) ⊆ interior (closure (A : Set X)) := hA
      exact Set.Subset.trans hA' subset_closure
    exact closure_minimal h₁ isClosed_closure
  · -- `closure (interior (closure A)) ⊆ closure A`
    have h₂ : interior (closure (A : Set X)) ⊆ closure (A : Set X) :=
      interior_subset (s := closure (A : Set X))
    simpa [closure_closure] using closure_mono h₂

theorem closure_eq_closure_interior_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  intro hA
  have hP3 : Topology.P3 (A : Set X) := Topology.P2_implies_P3 (A := A) hA
  exact closure_eq_closure_interior_closure_of_P3 (A := A) hP3

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  -- Using the equality of closures granted by `P1`
  have hEq := closure_eq_closure_interior_of_P1 (A := A) hA
  have hx_intA : (x : X) ∈ closure (interior (A : Set X)) := by
    simpa [hEq] using hx
  -- Monotonicity of closure with respect to set inclusion
  have h_subset :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
    apply closure_mono
    exact interior_subset_interior_closure (A := A)
  exact h_subset hx_intA

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔ closure (A : Set X) = closure (interior (A : Set X)) := by
  constructor
  · intro hA
    exact closure_eq_closure_interior_of_P1 (A := A) hA
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hx
    simpa [hEq] using hx_cl

theorem P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hClosureP3
  dsimp [Topology.P3] at hClosureP3 ⊢
  intro x hxA
  have hxClosure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have hxInterior : (x : X) ∈ interior (closure (closure (A : Set X))) :=
    hClosureP3 hxClosure
  simpa [closure_closure] using hxInterior

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x _
  simp [interior_univ, closure_univ]

theorem P3_interior_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (A : Set X)) ↔ Topology.P2 (interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P3_iff_P2_of_isOpen (A := interior (A : Set X)) hOpen)

theorem interior_closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) =
        interior (closure (interior (A : Set X))) := by
  intro hA
  have hEq : closure (A : Set X) = closure (interior (A : Set X)) :=
    closure_eq_closure_interior_of_P2 (A := A) hA
  simpa [hEq]

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X}
    (hf : ∀ i, Topology.P2 (f i)) :
    Topology.P2 (⋃ i, f i) := by
  dsimp [Topology.P2] at hf ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_int : (x : X) ∈ interior (closure (interior (f i))) := hf i hxi
  have h_subset :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ j, f j))) := by
    have h_closure :
        closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) := by
      apply closure_mono
      have h_int : interior (f i) ⊆ interior (⋃ j, f j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion.mpr ⟨i, hy⟩
      exact h_int
    exact interior_mono h_closure
  exact h_subset hx_int

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (A : Set X) = Set.univ) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x _
  simpa [hA, interior_univ] using (Set.mem_univ (x : X))

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X}
    (hf : ∀ i, Topology.P3 (f i)) :
    Topology.P3 (⋃ i, f i) := by
  dsimp [Topology.P3] at hf ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_int : (x : X) ∈ interior (closure (f i)) := hf i hxi
  have h_subset :
      interior (closure (f i)) ⊆ interior (closure (⋃ j, f j)) := by
    apply interior_mono
    have h_closure : closure (f i) ⊆ closure (⋃ j, f j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.mpr ⟨i, hy⟩
    exact h_closure
  exact h_subset hx_int

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  cases hx

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx

theorem interior_closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      interior (closure (A : Set X)) =
        interior (closure (interior (A : Set X))) := by
  intro hA
  have hEq : closure (A : Set X) = closure (interior (A : Set X)) :=
    closure_eq_closure_interior_of_P1 (A := A) hA
  simpa [hEq]

theorem P1_interior_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P3 (interior (A : Set X)) := by
  have h₁ := Topology.P1_interior_iff_P2_interior (A := A)
  have h₂ := Topology.P3_interior_iff_P2_interior (A := A)
  simpa using h₁.trans h₂.symm

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X}
    (hf : ∀ i, Topology.P1 (f i)) :
    Topology.P1 (⋃ i, f i) := by
  dsimp [Topology.P1] at hf ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_cl : (x : X) ∈ closure (interior (f i)) := hf i hxi
  have h_subset :
      closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) := by
    apply closure_mono
    have h_int : interior (f i) ⊆ interior (⋃ j, f j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.mpr ⟨i, hy⟩
    exact h_int
  exact h_subset hx_cl

theorem P1_interior_closure_iff_P2_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) ↔
      Topology.P2 (interior (closure (A : Set X))) := by
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen
      (A := interior (closure (A : Set X)))
      hOpen)

theorem P1_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    (Topology.P1_of_isOpen (A := interior (closure (interior A))) hOpen)

theorem closure_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (A : Set X)))) =
      closure (interior (A : Set X)) := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior (A : Set X)) := by
      -- `interior S` is always contained in `S`
      exact interior_subset (s := closure (interior (A : Set X)))
    have h₂ :
        closure (interior (closure (interior (A : Set X)))) ⊆
          closure (closure (interior (A : Set X))) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₁ :
        interior (A : Set X) ⊆
          interior (closure (interior (A : Set X))) := by
      apply interior_maximal
      · exact subset_closure
      · exact isOpen_interior
    have h₂ :
        closure (interior (A : Set X)) ⊆
          closure (interior (closure (interior (A : Set X)))) :=
      closure_mono h₁
    simpa using h₂

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (A : Set X))) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is contained in `interior (closure (interior A))`
  have h₁ :
      interior (A : Set X) ⊆ interior (closure (interior (A : Set X))) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  -- Taking closures preserves this inclusion
  have h₂ :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (interior (A : Set X)))) :=
    closure_mono h₁
  exact h₂ hx

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx

theorem P3_interior_closure_iff_P2_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (A : Set X))) ↔
      Topology.P2 (interior (closure (A : Set X))) := by
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa using
    (Topology.P3_iff_P2_of_isOpen
      (A := interior (closure (A : Set X))) hOpen)

theorem Topology.P2_iff_P1_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Reuse the existing equivalences between the properties under the openness assumption
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P3 A ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  constructor
  · intro hP2
    -- From `P2` we obtain `P1` and `P3` via the equivalences
    have hP1 : Topology.P1 A := (h₁.mpr) hP2
    have hP3 : Topology.P3 A := (h₂.mpr) hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    -- From `P1` we recover `P2`; `P3` is not needed for this direction
    exact h₁.mp hP1

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A : Set X, A ∈ 𝒜 → Topology.P2 A) :
    Topology.P2 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA𝒜, hxA⟩
  have hx_int : (x : X) ∈ interior (closure (interior A)) :=
    h𝒜 A hA𝒜 hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜 : Set X))) := by
    have h_closure :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜 : Set X)) := by
      apply closure_mono
      have h_int : interior A ⊆ interior (⋃₀ 𝒜 : Set X) := by
        apply interior_mono
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA𝒜, hy⟩
      exact h_int
    exact interior_mono h_closure
  exact h_subset hx_int

theorem interior_closure_eq_closure_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 (A : Set X) →
      interior (closure (A : Set X)) =
        interior (closure (interior (closure (A : Set X)))) := by
  intro hA
  have hEq := closure_eq_closure_interior_closure_of_P3 (A := A) hA
  simpa using congrArg interior hEq

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A : Set X, A ∈ 𝒜 → Topology.P3 A) :
    Topology.P3 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA𝒜, hxA⟩
  have hx_int : (x : X) ∈ interior (closure A) := h𝒜 A hA𝒜 hxA
  have h_subset :
      interior (closure A) ⊆
        interior (closure (⋃₀ 𝒜 : Set X)) := by
    apply interior_mono
    have h_closure :
        closure A ⊆ closure (⋃₀ 𝒜 : Set X) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.mpr ⟨A, hA𝒜, hy⟩
    exact h_closure
  exact h_subset hx_int

theorem P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (A : Set X)))) := by
  simpa using
    (P1_closure_interior (A := closure (A : Set X)))

theorem closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior ((A ∩ B) : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hA_sub : interior (A ∩ B : Set X) ⊆ interior A := by
    apply interior_mono
    exact Set.inter_subset_left
  have hB_sub : interior (A ∩ B : Set X) ⊆ interior B := by
    apply interior_mono
    exact Set.inter_subset_right
  have hxA : (x : X) ∈ closure (interior A) := (closure_mono hA_sub) hx
  have hxB : (x : X) ∈ closure (interior B) := (closure_mono hB_sub) hx
  exact And.intro hxA hxB

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A : Set X, A ∈ 𝒜 → Topology.P1 A) :
    Topology.P1 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA𝒜, hxA⟩
  have hx_cl : (x : X) ∈ closure (interior A) := h𝒜 A hA𝒜 hxA
  have h_subset :
      closure (interior A) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) := by
    apply closure_mono
    have h_int : interior A ⊆ interior (⋃₀ 𝒜 : Set X) := by
      apply interior_mono
      intro y hy
      exact Set.mem_sUnion.mpr ⟨A, hA𝒜, hy⟩
    exact h_int
  exact h_subset hx_cl

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior (A : Set X)) = Set.univ) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hA] using this

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x _
  have : (x : X) ∈ interior (closure (interior (A : Set X))) := by
    simpa [hA, interior_univ] using (Set.mem_univ (x : X))
  exact this

theorem interior_closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior ((A ∩ B) : Set X))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have hA :
      interior (closure (interior ((A ∩ B) : Set X))) ⊆
        interior (closure (interior A)) := by
    apply interior_mono
    have h_closure :
        closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior A) := by
      apply closure_mono
      have h_int :
          interior ((A ∩ B) : Set X) ⊆ interior A := by
        apply interior_mono
        exact Set.inter_subset_left
      exact h_int
    exact h_closure
  have hB :
      interior (closure (interior ((A ∩ B) : Set X))) ⊆
        interior (closure (interior B)) := by
    apply interior_mono
    have h_closure :
        closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior B) := by
      apply closure_mono
      have h_int :
          interior ((A ∩ B) : Set X) ⊆ interior B := by
        apply interior_mono
        exact Set.inter_subset_right
      exact h_int
    exact h_closure
  exact And.intro (hA hx) (hB hx)

theorem P1_interior_closure_iff_P3_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) ↔
      Topology.P3 (interior (closure (A : Set X))) := by
  have h₁ := P1_interior_closure_iff_P2_interior_closure (A := A)
  have h₂ := P3_interior_closure_iff_P2_interior_closure (A := A)
  simpa using h₁.trans h₂.symm

theorem interior_closure_interior_subset_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (A : Set X)) := by
  apply interior_mono
  exact closure_mono (interior_subset (s := A))

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hA
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hA
  exact Topology.P1_closure (A := A) hP1

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) →
      interior (closure (A : Set X)) = Set.univ := by
  intro h_dense
  simpa [h_dense, interior_univ]

theorem closure_union_interiors_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  have h_subset : (interior (A : Set X) ∪ interior B) ⊆ interior (A ∪ B) := by
    intro x hx
    cases hx with
    | inl hA =>
        have hA_subset : interior (A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact hA_subset hA
    | inr hB =>
        have hB_subset : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact hB_subset hB
  exact closure_mono h_subset

theorem interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (A : Set X))))) =
      interior (closure (interior (A : Set X))) := by
  have h := closure_interior_closure_interior (A := A)
  simpa using congrArg interior h

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  -- First, deduce that `closure A = Set.univ`.
  have h_closureA : closure (A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure A`
    have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset (s := A))
    -- Hence, `Set.univ ⊆ closure A`
    have : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      simpa [hA] using h_subset
    -- Combine the two inclusions to obtain equality
    exact Set.Subset.antisymm (Set.subset_univ _) this
  -- Apply the existing result for dense sets
  simpa using Topology.P3_of_dense (A := A) h_closureA

theorem interior_closure_interior_eq_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  apply Set.Subset.antisymm
  ·
    have h₁ :
        interior (closure (interior (closure (A : Set X))))
          ⊆ interior (closure (closure (A : Set X))) := by
      simpa using
        (interior_closure_interior_subset_interior_closure
          (A := closure (A : Set X)))
    simpa [closure_closure] using h₁
  ·
    have h₂ :
        interior (closure (A : Set X)) ⊆
          closure (interior (closure (A : Set X))) :=
      subset_closure
    have h₃ := interior_mono h₂
    simpa [interior_interior] using h₃

theorem closure_interior_eq_of_isClosed_and_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) (hP1 : Topology.P1 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  apply Set.Subset.antisymm
  · -- `closure (interior A) ⊆ A`
    have h : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset (s := A))
    simpa [hA_closed.closure_eq] using h
  · -- `A ⊆ closure (interior A)` follows from `P1`
    exact hP1

theorem P1_iff_closure_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (A : Set X) ↔ closure (interior (A : Set X)) = A := by
  constructor
  · intro hP1
    exact closure_interior_eq_of_isClosed_and_P1 (A := A) hA_closed hP1
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    have : (x : X) ∈ closure (interior (A : Set X)) := by
      simpa [hEq] using hx
    exact this

theorem interior_closure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure ((A ∩ B) : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  have hxA : (x : X) ∈ interior (closure (A : Set X)) := by
    have h_subset : closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
      apply closure_mono
      exact Set.inter_subset_left
    exact (interior_mono h_subset) hx
  have hxB : (x : X) ∈ interior (closure (B : Set X)) := by
    have h_subset : closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
      apply closure_mono
      exact Set.inter_subset_right
    exact (interior_mono h_subset) hx
  exact And.intro hxA hxB

theorem isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    IsOpen (A : Set X) := by
  -- From `P3` and the fact that `A` is closed, we have `A ⊆ interior A`.
  have h_subset : (A : Set X) ⊆ interior (A : Set X) := by
    have hP3' : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    simpa [hA_closed.closure_eq] using hP3'
  -- Hence `interior A = A`.
  have h_eq : interior (A : Set X) = A := by
    apply Set.Subset.antisymm
    · exact interior_subset (s := A)
    · exact h_subset
  -- `interior A` is open, so `A` is open as well.
  have : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa [h_eq] using this

theorem interior_closure_interior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior (A : Set X))) ∪
        interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_closure : closure (interior (A : Set X))
          ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_int : interior (A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact h_int
      exact (interior_mono h_closure) hA
  | inr hB =>
      have h_closure : closure (interior (B : Set X))
          ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_int : interior (B : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact h_int
      exact (interior_mono h_closure) hB

theorem P3_of_isClosed_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → Topology.P1 A := by
  intro hP3
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  exact Topology.P1_of_isOpen (A := A) hOpen

theorem P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P3]
  intro x hxA
  -- `x` is in `closure A`
  have hxClosure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  -- Apply `P2` for `closure A`
  have hxInt₁ :
      (x : X) ∈ interior (closure (interior (closure (A : Set X)))) :=
    hP2 hxClosure
  -- Use the inclusion
  have hSubset :
      interior (closure (interior (closure (A : Set X)))) ⊆
        interior (closure (A : Set X)) := by
    simpa using
      (interior_closure_interior_subset_interior_closure
        (A := closure (A : Set X)))
  exact hSubset hxInt₁

theorem Topology.P3_iff_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro hP3
    -- A closed set satisfying P3 is open, by a previous lemma.
    have hOpen : IsOpen (A : Set X) :=
      isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
    -- For open sets, P3 and P2 are equivalent.
    have hEquiv := Topology.P3_iff_P2_of_isOpen (A := A) hOpen
    exact hEquiv.mp hP3
  · intro hP2
    -- In general, P2 implies P3.
    exact Topology.P2_implies_P3 (A := A) hP2

theorem closure_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  simpa using
    (closure_interior_closure_interior (A := closure (A : Set X)))

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP2
    -- From `P2` we get `P3`.
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P2_implies_P3 (A := A) hP2
    -- A closed set satisfying `P3` is open.
    exact isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  · intro hOpen
    -- An open set automatically satisfies `P2`.
    exact Topology.P2_of_isOpen (A := A) hOpen

theorem P3_closure_iff_P2_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (A : Set X)) ↔ Topology.P2 (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P3_iff_P2_of_isClosed
      (A := closure (A : Set X)) hClosed)

theorem interior_closure_eq_univ_iff_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      intro x _
      have hx : (x : X) ∈ interior (closure (A : Set X)) := by
        simpa [hInt] using (Set.mem_univ (x : X))
      exact (interior_subset (s := closure (A : Set X))) hx
    exact Set.Subset.antisymm (Set.subset_univ _) hSub
  · intro hCl
    exact interior_closure_eq_univ_of_dense (A := A) hCl

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 A ↔ IsOpen (A : Set X) := by
  have h₁ := Topology.P3_iff_P2_of_isClosed (A := A) hA_closed
  have h₂ := Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed
  simpa using h₁.trans h₂

theorem P3_closure_interior_iff_P2_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P3 (closure (interior (A : Set X))) ↔
      Topology.P2 (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P3_iff_P2_of_isClosed
      (A := closure (interior (A : Set X))) hClosed)

theorem P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (A := closure (A : Set X)) hClosed)

theorem P2_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using Topology.P2_of_isOpen (A := A ∩ B) hOpen

theorem P1_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using (P1_of_isOpen (A := A ∩ B) hOpen)

theorem P1_univ_iff_P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ↔ Topology.P2 (Set.univ : Set X) := by
  constructor
  · intro _; simpa using (Topology.P2_univ (X := X))
  · intro _; simpa using (Topology.P1_univ (X := X))

theorem P1_P2_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 (A : Set X) := P1_of_isOpen (A := A) hA
  have hP2 : Topology.P2 (A : Set X) := P2_of_isOpen (A := A) hA
  have hP3 : Topology.P3 (A : Set X) := P3_of_isOpen (A := A) hA
  exact ⟨hP1, hP2, hP3⟩

theorem interior_closure_interior_eq_univ_iff_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (Set.univ : Set X) ↔
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  simpa using
    (interior_closure_eq_univ_iff_dense
      (A := interior (A : Set X)))

theorem isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    IsOpen (A : Set X) := by
  -- First, derive `P3` from `P2`.
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  -- A set that is both closed and satisfies `P3` is open.
  exact isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hP3
  -- `hP3` gives the inclusion `A ⊆ interior (closure A)`
  dsimp [Topology.P3] at hP3
  -- Unfold the goal `P1 (closure A)`
  dsimp [Topology.P1]
  intro x hx
  -- Taking closures preserves inclusions
  have h_incl :
      closure (A : Set X) ⊆ closure (interior (closure (A : Set X))) :=
    closure_mono hP3
  exact h_incl hx

theorem interior_closure_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (A : Set X))) = interior (closure (A : Set X)) := by
  simpa [closure_closure]

theorem P3_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using (Topology.P3_of_isOpen (A := A ∩ B) hOpen)

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (interior (B : Set X))) := by
  exact interior_mono (closure_mono (interior_mono hAB))

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ⊆ closure A := by
  exact closure_mono (interior_subset (s := A))

theorem P1_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  exact P1_of_isOpen (A := A) hOpen

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ⊆
      closure (interior (closure (A : Set X))) := by
  apply closure_mono
  exact interior_subset_interior_closure (A := A)

theorem closure_interior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure (A : Set X) := by
  simpa [hA.interior_eq]

theorem closure_union_interiors_eq_union_closure_interiors
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure ((interior (A : Set X)) ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  -- We prove the equality by showing mutual inclusion.
  apply Set.Subset.antisymm
  · -- First, `closure (U ∪ V)` is contained in `closure U ∪ closure V`.
    have h_subset :
        (interior (A : Set X) ∪ interior B) ⊆
          closure (interior A) ∪ closure (interior B) := by
      intro x hx
      cases hx with
      | inl hA =>
          exact Or.inl (subset_closure hA)
      | inr hB =>
          exact Or.inr (subset_closure hB)
    have h_closed :
        IsClosed (closure (interior A) ∪ closure (interior B)) := by
      exact (isClosed_closure).union isClosed_closure
    exact closure_minimal h_subset h_closed
  · -- Conversely, each of the two closures lies inside `closure (U ∪ V)`.
    intro x hx
    cases hx with
    | inl hA =>
        have h_sub :
            closure (interior A) ⊆
              closure ((interior (A : Set X)) ∪ interior B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact h_sub hA
    | inr hB =>
        have h_sub :
            closure (interior B) ⊆
              closure ((interior (A : Set X)) ∪ interior B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact h_sub hB

theorem P3_univ_iff_P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) ↔ Topology.P2 (Set.univ : Set X) := by
  constructor
  · intro _; exact Topology.P2_univ (X := X)
  · intro _; exact Topology.P3_univ (X := X)

theorem P1_univ_iff_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ↔ Topology.P3 (Set.univ : Set X) := by
  have h₁ := Topology.P1_univ_iff_P2_univ (X := X)
  have h₂ := Topology.P3_univ_iff_P2_univ (X := X)
  simpa using h₁.trans h₂.symm

theorem interior_closure_eq_interior_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior (A : Set X) := by
  simpa [hA.closure_eq]

theorem P1_empty_iff_P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) := by
  constructor
  · intro _
    exact Topology.P2_empty (X := X)
  · intro _
    exact Topology.P1_empty (X := X)

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  exact interior_mono (closure_mono hAB)

theorem isClosed_of_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = A → IsClosed (A : Set X) := by
  intro hA
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa [hA] using hClosed

theorem interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : closure (A : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact (interior_mono hSub) hA
  | inr hB =>
      have hSub : closure (B : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      exact (interior_mono hSub) hB

theorem isOpen_of_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = A → IsOpen (A : Set X) := by
  intro hA
  have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa [hA] using this

theorem P2_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    Topology.P2 A := by
  have hEquiv := Topology.P3_iff_P2_of_isClosed (A := A) hA_closed
  exact hEquiv.mp hP3

theorem interior_inter_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆
      interior (A : Set X) ∩ interior (B : Set X) := by
  intro x hx
  have hxA : (x : X) ∈ interior (A : Set X) := by
    have hSubset : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    exact (interior_mono hSubset) hx
  have hxB : (x : X) ∈ interior (B : Set X) := by
    have hSubset : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact (interior_mono hSubset) hx
  exact And.intro hxA hxB

theorem closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (Set.univ : Set X) →
      closure (A : Set X) = (Set.univ : Set X) := by
  intro h_dense_int
  -- `closure (interior A)` is always contained in `closure A`
  have h_subset : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset (s := A))
  -- Hence `Set.univ ⊆ closure A`
  have : (Set.univ : Set X) ⊆ closure A := by
    simpa [h_dense_int] using h_subset
  -- Combine the two inclusions to obtain equality
  exact Set.Subset.antisymm (Set.subset_univ _) this

theorem interior_union_eq_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa [hOpen.interior_eq]

theorem closure_interior_closure_eq_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (interior (closure (A : Set X))) =
        closure (interior (A : Set X)) := by
  intro hA
  have hEq := closure_eq_closure_interior_of_P1 (A := A) hA
  calc
    closure (interior (closure (A : Set X)))
        = closure (interior (closure (interior (A : Set X)))) := by
          simpa [hEq]
    _ = closure (interior (A : Set X)) := by
          simpa using closure_interior_closure_interior (A := A)

theorem closure_interior_eq_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- A set that is both closed and satisfies `P2` is open.
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  -- Hence `interior A = A`.
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  -- Use the facts that `closure A = A` (since `A` is closed) and `interior A = A`.
  calc
    closure (interior (A : Set X))
        = closure (A : Set X) := by
          simpa [hInt]
    _ = A := hA_closed.closure_eq

theorem openInterInterior_subset_and_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) :
    (A ∩ interior (B : Set X) : Set X) ⊆ A ∩ B ∧
      IsOpen (A ∩ interior (B : Set X)) := by
  refine And.intro ?_ ?_
  · -- Subset part
    intro x hx
    rcases hx with ⟨hAx, hIntBx⟩
    have hBx : (x : X) ∈ (B : Set X) :=
      interior_subset (s := B) hIntBx
    exact And.intro hAx hBx
  · -- Openness part
    exact hA.inter isOpen_interior

theorem interior_inter_eq_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using hOpen.interior_eq

theorem P3_closure_interior_iff_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (A := closure (interior (A : Set X))) hClosed)

theorem P2_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P2 (interior (closure (interior (closure (A : Set X))))) := by
  have hOpen :
      IsOpen (interior (closure (interior (closure (A : Set X))))) :=
    isOpen_interior
  simpa using
    (Topology.P2_of_isOpen
      (A := interior (closure (interior (closure (A : Set X))))) hOpen)

theorem interior_closure_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) =
        interior (closure (interior (closure (A : Set X)))) := by
  intro hP2
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  exact interior_closure_eq_closure_interior_closure_of_P3 (A := A) hP3

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) := by
  exact closure_mono (interior_mono hAB)

theorem isOpen_of_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = A → IsOpen (A : Set X) := by
  intro hA
  have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa [hA] using this

theorem P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (A := closure (A : Set X)) hClosed)

theorem closure_inter_subset_inter_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  have hxA : (x : X) ∈ closure (A : Set X) := by
    have hSubset : ((A ∩ B) : Set X) ⊆ A := Set.inter_subset_left
    exact (closure_mono hSubset) hx
  have hxB : (x : X) ∈ closure (B : Set X) := by
    have hSubset : ((A ∩ B) : Set X) ⊆ B := Set.inter_subset_right
    exact (closure_mono hSubset) hx
  exact And.intro hxA hxB

theorem P1_of_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure (interior (A : Set X)) = A) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hxA
  have : (x : X) ∈ closure (interior (A : Set X)) := by
    simpa [hEq] using hxA
  exact this

theorem interior_closure_interior_double_idempotent {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
      interior (closure (interior (A : Set X))) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))
        = interior (closure (interior (closure (interior (A : Set X))))) := by
          simpa using
            interior_closure_interior_idempotent
              (A := closure (interior (A : Set X)))
    _ = interior (closure (interior (A : Set X))) := by
          simpa using
            interior_closure_interior_idempotent (A := A)

theorem interior_eq_self_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    interior (A : Set X) = A := by
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  simpa using hOpen.interior_eq

theorem closure_eq_closure_interior_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (A : Set X) =
        closure (interior (closure (A : Set X))) := by
  intro hP1
  -- `closure A = closure (interior A)` via `P1`
  have h₁ := closure_eq_closure_interior_of_P1 (A := A) hP1
  -- `closure (interior (closure A)) = closure (interior A)` via `P1`
  have h₂ := closure_interior_closure_eq_closure_interior_of_P1 (A := A) hP1
  calc
    closure (A : Set X)
        = closure (interior (A : Set X)) := h₁
    _ = closure (interior (closure (A : Set X))) := by
        simpa using h₂.symm

theorem closure_interiors_union_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    (closure (interior (A : Set X)) ∪ closure (interior B)) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_subset :
          closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior (A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hA
  | inr hB =>
      have h_subset :
          closure (interior (B : Set X)) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior (B : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hB

theorem Set.interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_sub : interior (A : Set X) ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_sub hA
  | inr hB =>
      have h_sub : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_sub hB

theorem closure_union_eq_union_closure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure ((A ∪ B) : Set X) = closure (A : Set X) ∪ closure (B : Set X) := by
  apply Set.Subset.antisymm
  · -- `closure (A ∪ B) ⊆ closure A ∪ closure B`
    have h_subset : (A ∪ B : Set X) ⊆ closure (A : Set X) ∪ closure (B : Set X) := by
      intro x hx
      cases hx with
      | inl hA => exact Or.inl (subset_closure hA)
      | inr hB => exact Or.inr (subset_closure hB)
    have h_closed : IsClosed (closure (A : Set X) ∪ closure (B : Set X)) :=
      (isClosed_closure).union isClosed_closure
    exact closure_minimal h_subset h_closed
  · -- `closure A ∪ closure B ⊆ closure (A ∪ B)`
    intro x hx
    cases hx with
    | inl hA =>
        have h : closure (A : Set X) ⊆ closure ((A ∪ B) : Set X) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact h hA
    | inr hB =>
        have h : closure (B : Set X) ⊆ closure ((A ∪ B) : Set X) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact h hB



theorem P3_empty_iff_P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) := by
  have hOpen : IsOpen (∅ : Set X) := isOpen_empty
  simpa using
    (Topology.P3_iff_P2_of_isOpen (A := (∅ : Set X)) hOpen)

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ⊆ interior (closure (interior (A : Set X))) := by
  apply interior_maximal
  · exact subset_closure
  · exact isOpen_interior

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  exact closure_mono (interior_mono (closure_mono hAB))

theorem closure_interior_eq_self_of_isOpen_and_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hOpen : IsOpen (A : Set X))
    (hClosed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  have hCl : closure (A : Set X) = A := hClosed.closure_eq
  calc
    closure (interior (A : Set X))
        = closure (A : Set X) := by
          simpa [hInt]
    _ = A := hCl

theorem inter_interiors_subset_interior_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    (interior (A : Set X)) ∩ interior B ⊆ interior ((A ∩ B) : Set X) := by
  have hSubset : (interior (A : Set X)) ∩ interior B ⊆ (A : Set X) ∩ B := by
    intro x hx
    rcases hx with ⟨hA, hB⟩
    exact And.intro (interior_subset hA) (interior_subset hB)
  have hOpen : IsOpen ((interior (A : Set X)) ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  exact interior_maximal hSubset hOpen

theorem P1_empty_iff_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔ Topology.P3 (∅ : Set X) := by
  have h₁ : Topology.P1 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) :=
    P1_empty_iff_P2_empty (X := X)
  have h₂ : Topology.P3 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) :=
    P3_empty_iff_P2_empty (X := X)
  simpa using h₁.trans h₂.symm

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  -- First, `x` belongs to the closure of `A`.
  have hxClosure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  -- Since `closure A` is open, its interior is itself.
  have hxInterior : (x : X) ∈ interior (closure (A : Set X)) := by
    simpa [hOpen.interior_eq] using hxClosure
  exact hxInterior

theorem P1_iff_P1_closure_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 A ↔ Topology.P1 (closure (A : Set X)) := by
  simpa [hA_closed.closure_eq]

theorem interior_eq_self_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    interior (A : Set X) = A := by
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  simpa using hOpen.interior_eq

theorem closure_inter_eq_inter_closure_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = closure (A : Set X) ∩ closure (B : Set X) := by
  simpa [hA_closed.closure_eq, hB_closed.closure_eq,
        (hA_closed.inter hB_closed).closure_eq]

theorem closure_interior_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior (A : Set X))) =
      closure (interior (A : Set X)) := by
  simpa [interior_interior]

theorem P2_inter_interior {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P2 (interior (A : Set X) ∩ interior B) := by
  -- Both `interior A` and `interior B` are open sets.
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hB : IsOpen (interior (B : Set X)) := isOpen_interior
  -- Apply the lemma for the intersection of two open sets.
  simpa using
    (Topology.P2_inter_of_isOpen
        (A := interior (A : Set X)) (B := interior (B : Set X)) hA hB)

theorem P2_closure_interior_iff_isOpen_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P2 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  have h₁ :=
    (P3_closure_interior_iff_P2_closure_interior (A := A))
  have h₂ :=
    (P3_closure_interior_iff_isOpen_closure_interior (A := A))
  simpa using h₁.symm.trans h₂

theorem closure_interior_eq_univ_of_P1_and_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (A : Set X) = (Set.univ : Set X) →
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  intro hP1 hDense
  have hEq := closure_eq_closure_interior_of_P1 (A := A) hP1
  calc
    closure (interior (A : Set X))
        = closure (A : Set X) := by
          simpa using hEq.symm
    _ = (Set.univ : Set X) := hDense

theorem interior_closure_interior_closure_subset_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) ⊆
      interior (closure (A : Set X)) := by
  simpa [closure_closure] using
    interior_closure_interior_subset_interior_closure
      (A := closure (A : Set X))

theorem P3_inter_interior {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P3 (interior (A : Set X) ∩ interior B) := by
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hB : IsOpen (interior (B : Set X)) := isOpen_interior
  simpa using
    (Topology.P3_inter_of_isOpen
        (A := interior (A : Set X)) (B := interior (B : Set X)) hA hB)

theorem P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (closure (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx
  -- Since `A` is open and `A ⊆ closure A`, we have `A ⊆ interior (closure A)`.
  have hA_subset : (A : Set X) ⊆ interior (closure (A : Set X)) := by
    apply interior_maximal
    · exact subset_closure
    · exact hA
  -- Taking closures preserves this inclusion.
  have h_closure_subset :
      closure (A : Set X) ⊆
        closure (interior (closure (A : Set X))) :=
    closure_mono hA_subset
  exact h_closure_subset hx

theorem closure_inter_interior_subset_closure_interiors {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ interior (B : Set X)) : Set X) ⊆
      closure (A : Set X) ∩ closure (interior (B : Set X)) := by
  intro x hx
  have hA : ((A : Set X) ∩ interior (B : Set X)) ⊆ A := by
    intro y hy
    exact hy.1
  have hxA : (x : X) ∈ closure (A : Set X) := (closure_mono hA) hx
  have hB : ((A : Set X) ∩ interior (B : Set X)) ⊆ interior (B : Set X) := by
    intro y hy
    exact hy.2
  have hxB : (x : X) ∈ closure (interior (B : Set X)) := (closure_mono hB) hx
  exact And.intro hxA hxB

theorem interior_subset_closure_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hx
  exact subset_closure (interior_subset hx)

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (A : Set X))) ⊆ closure (A : Set X) := by
  intro x hx
  -- From `hx`, we know `x` lies in the closure of `interior A`.
  have hx_closure_int : (x : X) ∈ closure (interior (A : Set X)) :=
    interior_subset (s := closure (interior (A : Set X))) hx
  -- `closure (interior A)` is contained in `closure A`.
  have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset (s := A))
  -- Combining the facts yields the desired inclusion.
  exact h_subset hx_closure_int

theorem isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior (A : Set X)) := by
  -- Express the set as an intersection of two closed sets
  have h_eq :
      (closure (A : Set X) \ interior (A : Set X)) =
        closure (A : Set X) ∩ (interior (A : Set X))ᶜ := by
    rfl
  -- `closure A` is closed
  have h_closure : IsClosed (closure (A : Set X)) := isClosed_closure
  -- The complement of `interior A` is closed because `interior A` is open
  have h_compl : IsClosed ((interior (A : Set X))ᶜ) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  -- The intersection of two closed sets is closed
  simpa [h_eq] using h_closure.inter h_compl

theorem Topology.P2_iff_P1_and_P3_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact ⟨Topology.P2_implies_P1 (A := A) hP2,
      Topology.P2_implies_P3 (A := A) hP2⟩
  · rintro ⟨_, hP3⟩
    have hOpen : IsOpen (A : Set X) :=
      isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
    exact Topology.P2_of_isOpen (A := A) hOpen



theorem interior_closure_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (interior (A : Set X)))) =
      interior (closure (interior (A : Set X))) := by
  simpa using
    (interior_closure_closure (A := interior (A : Set X)))

theorem interior_inter_eq_of_isOpen_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) :
    interior (A ∩ B : Set X) = A ∩ interior (B : Set X) := by
  apply Set.Subset.antisymm
  · -- `interior (A ∩ B) ⊆ A ∩ interior B`
    intro x hx
    have hAB : (x : X) ∈ (A ∩ B : Set X) := interior_subset hx
    have hA_mem : (x : X) ∈ A := hAB.1
    -- Monotonicity of `interior`
    have h_intB : (x : X) ∈ interior (B : Set X) := by
      have h_subset : (A ∩ B : Set X) ⊆ (B : Set X) := Set.inter_subset_right
      exact (interior_mono h_subset) hx
    exact And.intro hA_mem h_intB
  · -- `A ∩ interior B ⊆ interior (A ∩ B)`
    intro x hx
    rcases hx with ⟨hA_mem, h_intB⟩
    -- The open set `A ∩ interior B` contains `x` and lies inside `A ∩ B`
    have h_open : IsOpen (A ∩ interior (B : Set X)) := hA.inter isOpen_interior
    have hx_open : (x : X) ∈ (A ∩ interior (B : Set X)) :=
      And.intro hA_mem h_intB
    have hx_int_open : (x : X) ∈ interior (A ∩ interior (B : Set X)) := by
      simpa [h_open.interior_eq] using hx_open
    have h_subset : (A ∩ interior (B : Set X)) ⊆ A ∩ B := by
      intro y hy
      exact And.intro hy.1 (interior_subset hy.2)
    exact (interior_mono h_subset) hx_int_open

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Existing equivalences under the openness assumption.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  -- Prove the desired equivalence.
  constructor
  · intro hP1
    exact ⟨h₁.mp hP1, h₂.mp hP1⟩
  · rintro ⟨hP2, _⟩
    exact h₁.mpr hP2

theorem P2_closure_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3
  simpa using ((P3_closure_iff_P2_closure (A := A)).1 hP3)

theorem closure_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior (A : Set X))) = closure (interior (A : Set X)) := by
  simpa [closure_closure]

theorem interior_inter_eq_of_isOpen_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = interior (A : Set X) ∩ B := by
  apply Set.Subset.antisymm
  · -- `interior (A ∩ B) ⊆ interior A ∩ B`
    intro x hx
    have hAB : (x : X) ∈ (A ∩ B : Set X) := interior_subset hx
    -- `x` belongs to `interior A`
    have hIntA : (x : X) ∈ interior (A : Set X) := by
      have h_subset : (A ∩ B : Set X) ⊆ (A : Set X) := Set.inter_subset_left
      exact (interior_mono h_subset) hx
    exact And.intro hIntA hAB.2
  · -- `interior A ∩ B ⊆ interior (A ∩ B)`
    intro x hx
    rcases hx with ⟨hIntA, hBx⟩
    -- The open set `interior A ∩ B` contains `x`
    have hOpen : IsOpen (interior (A : Set X) ∩ B) :=
      isOpen_interior.inter hB
    have hxOpen : (x : X) ∈ interior (A : Set X) ∩ B :=
      And.intro hIntA hBx
    have hxIntOpen : (x : X) ∈ interior (interior (A : Set X) ∩ B) := by
      simpa [hOpen.interior_eq] using hxOpen
    -- `interior A ∩ B ⊆ A ∩ B`
    have h_subset : (interior (A : Set X) ∩ B) ⊆ (A ∩ B : Set X) := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    exact (interior_mono h_subset) hxIntOpen

theorem closure_closure_diff_interior_eq_self {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (closure (A : Set X) \ interior (A : Set X)) =
      closure (A : Set X) \ interior (A : Set X) := by
  have hClosed :
      IsClosed (closure (A : Set X) \ interior (A : Set X)) :=
    isClosed_closure_diff_interior (A := A)
  simpa using hClosed.closure_eq

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : (A : Set X).Nonempty) (hP1 : Topology.P1 (A : Set X)) :
    (interior (A : Set X)).Nonempty := by
  classical
  rcases hA with ⟨x, hxA⟩
  have hx_cl : (x : X) ∈ closure (interior (A : Set X)) := hP1 hxA
  by_cases hInt : (interior (A : Set X)).Nonempty
  · exact hInt
  · -- If `interior A` were empty, `x` would lie in `closure ∅ = ∅`, contradiction.
    have hInt_eq_empty : interior (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hInt
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hInt_eq_empty, closure_empty] using hx_cl
    cases this

theorem interior_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior (closure (A : Set X))) = interior (closure (A : Set X)) := by
  simpa [interior_interior]

theorem closure_inter_interiors_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior A ∩ interior B` is contained in `interior A`
  have hA_sub : interior (A : Set X) ∩ interior B ⊆ interior A := by
    intro y hy
    exact hy.1
  -- `interior A ∩ interior B` is contained in `interior B`
  have hB_sub : interior (A : Set X) ∩ interior B ⊆ interior B := by
    intro y hy
    exact hy.2
  -- Hence, their closures satisfy the desired inclusions
  have hxA : (x : X) ∈ closure (interior A) := (closure_mono hA_sub) hx
  have hxB : (x : X) ∈ closure (interior B) := (closure_mono hB_sub) hx
  exact And.intro hxA hxB

theorem P1_and_P3_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = interior (A : Set X) →
      (Topology.P1 A ∧ Topology.P3 A) := by
  intro hEq
  -- First, note that every point of `A` lies in `interior A`,
  -- since `A ⊆ closure A = interior A`.
  have hA_subset_int : (A : Set X) ⊆ interior (A : Set X) := by
    intro x hx
    have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hx
    simpa [hEq] using hx_cl
  -- Prove `P1`.
  have hP1 : Topology.P1 (A : Set X) := by
    dsimp [Topology.P1]
    intro x hx
    have hx_int : (x : X) ∈ interior (A : Set X) := hA_subset_int hx
    exact subset_closure hx_int
  -- Prove `P3`.
  have hP3 : Topology.P3 (A : Set X) := by
    dsimp [Topology.P3]
    intro x hx
    have hx_int : (x : X) ∈ interior (A : Set X) := hA_subset_int hx
    simpa [hEq, interior_interior] using hx_int
  exact And.intro hP1 hP3

theorem P1_nested_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior (closure (interior (A : Set X)))))) := by
  -- The set under consideration is an interior, hence open.
  have hOpen :
      IsOpen (interior (closure (interior (closure (interior A))))) :=
    isOpen_interior
  -- Any open set satisfies `P1`.
  simpa using
    (Topology.P1_of_isOpen
      (A := interior (closure (interior (closure (interior A))))) hOpen)

theorem interior_closure_union_eq_union_closure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    interior (closure ((A ∪ B) : Set X)) =
      interior (closure (A : Set X) ∪ closure (B : Set X)) := by
  have h := closure_union_eq_union_closure (A := A) (B := B)
  simpa using congrArg interior h

theorem interior_subset_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hx
  exact subset_closure hx

theorem closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]

theorem P3_union_right_dense {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (A : Set X) →
      closure (B : Set X) = (Set.univ : Set X) →
      Topology.P3 (A ∪ B) := by
  intro hP3A hDenseB
  have hP3B : Topology.P3 (B : Set X) :=
    Topology.P3_of_dense (A := B) hDenseB
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : (A : Set X).Nonempty) (hP2 : Topology.P2 (A : Set X)) :
    (interior (A : Set X)).Nonempty := by
  classical
  by_contra hInt
  -- If `interior A` is empty, derive a contradiction with `P2`.
  have hInt_empty : interior (A : Set X) = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  rcases hA with ⟨x, hxA⟩
  have hxInt : (x : X) ∈ interior (closure (interior (A : Set X))) :=
    hP2 hxA
  have : (x : X) ∈ (∅ : Set X) := by
    simpa [hInt_empty] using hxInt
  exact this

theorem interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X).Nonempty → Topology.P3 (A : Set X) →
      (interior (closure (A : Set X))).Nonempty := by
  intro hA hP3
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩

theorem interior_closure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {f : ι → Set X} :
    (⋃ i, interior (closure (f i : Set X))) ⊆
      interior (closure (⋃ i, f i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have h_closure :
      closure (f i : Set X) ⊆ closure (⋃ j, f j : Set X) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  have h_interior :
      interior (closure (f i : Set X)) ⊆
        interior (closure (⋃ j, f j : Set X)) :=
    interior_mono h_closure
  exact h_interior hxi

theorem Topology.P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _; exact Topology.P2_of_dense_interior (A := A) h_dense
  · intro hP2; exact Topology.P2_implies_P1 (A := A) hP2

theorem closure_interior_closure_interior_double_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
      closure (interior (A : Set X)) := by
  calc
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
        closure (interior (closure (interior (A : Set X)))) := by
          simpa using
            closure_interior_closure_interior
              (A := closure (interior (A : Set X)))
    _ = closure (interior (A : Set X)) := by
          simpa using
            closure_interior_closure_interior (A := A)

theorem closure_eq_interior_union_closure_diff_interior {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) =
      interior (A : Set X) ∪ (closure (A : Set X) \ interior (A : Set X)) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases h_int : (x : X) ∈ interior (A : Set X)
    · exact Or.inl h_int
    · exact Or.inr ⟨hx, h_int⟩
  · intro x hx
    cases hx with
    | inl h_int =>
        -- `x` lies in `interior A`, hence in `A` and thus in `closure A`.
        have hA : (x : X) ∈ (A : Set X) := interior_subset h_int
        exact subset_closure hA
    | inr h_cl =>
        exact h_cl.1

theorem closure_iUnion_subset_closure {X : Type*} [TopologicalSpace X] {ι : Sort _}
    (f : ι → Set X) :
    (⋃ i, closure (f i : Set X)) ⊆ closure (⋃ i, f i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have h_mono : closure (f i : Set X) ⊆ closure (⋃ j, f j : Set X) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  exact h_mono hxi

theorem closure_interior_eq_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- From `P3` and the fact that `A` is closed, deduce `P2`.
  have hP2 : Topology.P2 (A : Set X) :=
    Topology.P2_of_isClosed_and_P3 (A := A) hA_closed hP3
  -- Apply the existing result that relates `P2`, closedness, and the desired equality.
  exact closure_interior_eq_of_isClosed_and_P2 (A := A) hA_closed hP2

theorem P3_union_left_dense {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) = (Set.univ : Set X) →
      Topology.P3 (A ∪ B) := by
  intro hDenseA
  -- First, show that the union has dense closure.
  have hCl : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    have hEq := closure_union_eq_union_closure (A := A) (B := B)
    simpa [hDenseA, Set.union_univ, Set.univ_union] using hEq
  -- Apply the existing lemma for dense sets.
  exact Topology.P3_of_dense (A := A ∪ B) hCl

theorem interior_closure_eq_self_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  -- First, `P3` together with closedness gives `interior A = A`.
  have hInt : interior (A : Set X) = A :=
    interior_eq_self_of_isClosed_and_P3 (A := A) hA_closed hP3
  -- For closed sets, `interior (closure A) = interior A`.
  have hIntCl : interior (closure (A : Set X)) = interior (A : Set X) :=
    interior_closure_eq_interior_of_isClosed (A := A) hA_closed
  -- Combine the two equalities.
  simpa [hInt] using hIntCl

theorem Topology.P3_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro _hP3
    exact Topology.P2_of_dense_interior (A := A) h_dense
  · intro hP2
    exact Topology.P2_implies_P3 (A := A) hP2

theorem closure_iInter_subset_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} :
    closure (⋂ i, f i : Set X) ⊆ ⋂ i, closure (f i) := by
  intro x hx
  apply Set.mem_iInter.2
  intro i
  exact (closure_mono (Set.iInter_subset _ _)) hx

theorem interior_inter_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hA, hAc⟩
    have hA_mem : (x : X) ∈ A := interior_subset hA
    have hAc_mem : (x : X) ∈ (Aᶜ) := interior_subset hAc
    exact (hAc_mem hA_mem).elim
  · exact Set.empty_subset _

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X).Nonempty → Topology.P2 (A : Set X) →
      (interior (closure (A : Set X))).Nonempty := by
  intro hA hP2
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  exact interior_closure_nonempty_of_P3 (A := A) hA hP3

theorem closure_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (A : Set X) ⊆ A := by
  set_option maxRecDepth 20000 in
  simpa [hA.closure_eq]

theorem Topology.P1_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h₁ := Topology.P1_iff_P2_of_dense_interior (A := A) h_dense
  have h₂ := Topology.P3_iff_P2_of_dense_interior (A := A) h_dense
  simpa using h₁.trans h₂.symm

theorem interior_closure_iInter_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} :
    interior (closure (⋂ i, f i : Set X)) ⊆ ⋂ i, interior (closure (f i : Set X)) := by
  intro x hx
  -- We will show that `x` belongs to each `interior (closure (f i))`.
  apply Set.mem_iInter.2
  intro i
  -- First, note `closure (⋂ i, f i) ⊆ closure (f i)`.
  have h_subset : closure (⋂ i, f i : Set X) ⊆ closure (f i : Set X) := by
    apply closure_mono
    intro y hy
    -- An element of the intersection belongs to every `f i`.
    have h_mem : (y : X) ∈ ⋂ i, f i := hy
    exact (Set.mem_iInter.mp h_mem) i
  -- Monotonicity of `interior` gives the desired inclusion.
  exact (interior_mono h_subset) hx

theorem closure_subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro hP1
  exact closure_minimal hP1 isClosed_closure

theorem interior_inter_eq_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((A ∩ B) : Set X) =
      interior (A : Set X) ∩ interior (B : Set X) := by
  apply Set.Subset.antisymm
  · exact interior_inter_subset_interiors (A := A) (B := B)
  · intro x hx
    exact (inter_interiors_subset_interior_inter (A := A) (B := B)) hx

theorem closure_interior_subset_interior_closure_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) →
      closure (interior (A : Set X)) ⊆ interior (closure (A : Set X)) := by
  intro hP3
  -- Unfold the definition of `P3` for `closure A`.
  dsimp [Topology.P3] at hP3
  -- We show that every point of `closure (interior A)` lies in `interior (closure A)`.
  intro x hxInt
  -- First, `x` belongs to `closure A`, by monotonicity of `closure`.
  have hxCl : (x : X) ∈ closure (A : Set X) :=
    (closure_interior_subset_closure (A := A)) hxInt
  -- Apply `P3` for `closure A`.
  have hxIntCl :
      (x : X) ∈ interior (closure (closure (A : Set X))) :=
    hP3 hxCl
  -- Simplify the double closure.
  simpa [closure_closure] using hxIntCl

theorem closure_union_eq_univ_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : closure (A : Set X) = (Set.univ : Set X)) :
    closure ((A ∪ B) : Set X) = (Set.univ : Set X) := by
  have h := closure_union_eq_union_closure (A := A) (B := B)
  simpa [hA, Set.union_univ, Set.univ_union] using h

theorem P2_interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (interior (A : Set X))) := by
  simpa using
    (P2_interior (X := X) (A := interior (A : Set X)))

theorem interior_closure_inter_closures_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  have hA : (x : X) ∈ interior (closure (A : Set X)) := by
    have hSubset :
        closure (A : Set X) ∩ closure (B : Set X) ⊆ closure (A : Set X) := by
      intro y hy; exact hy.1
    exact (interior_mono hSubset) hx
  have hB : (x : X) ∈ interior (closure (B : Set X)) := by
    have hSubset :
        closure (A : Set X) ∩ closure (B : Set X) ⊆ closure (B : Set X) := by
      intro y hy; exact hy.2
    exact (interior_mono hSubset) hx
  exact And.intro hA hB

theorem closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- First, we know `closure (interior A) ⊆ closure A`.
  have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_interior_subset_closure (A := A)
  -- Since `A` is closed, `closure A = A`, yielding the desired inclusion.
  simpa [hA_closed.closure_eq] using h_subset

theorem closure_union_eq_univ_of_dense_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (B : Set X) = (Set.univ : Set X) →
      closure ((A ∪ B) : Set X) = (Set.univ : Set X) := by
  intro hB
  have h := closure_union_eq_univ_of_dense_left (A := B) (B := A) hB
  simpa [Set.union_comm] using h

theorem interior_iInter_subset_iInter_interior {X : Type*} [TopologicalSpace X]
    {ι : Sort _} (f : ι → Set X) :
    interior (⋂ i, f i : Set X) ⊆ ⋂ i, interior (f i : Set X) := by
  intro x hx
  -- We show that `x` belongs to every `interior (f i)`.
  apply Set.mem_iInter.2
  intro i
  -- `⋂ i, f i` is contained in `f i`.
  have h_subset : (⋂ i, f i : Set X) ⊆ f i := Set.iInter_subset _ _
  -- Monotonicity of `interior` yields the desired inclusion.
  have h_interior : interior (⋂ i, f i : Set X) ⊆ interior (f i : Set X) :=
    interior_mono h_subset
  exact h_interior hx

theorem closure_interior_nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    (closure (interior (A : Set X))).Nonempty ↔
      (interior (A : Set X)).Nonempty := by
  classical
  constructor
  · intro h_closure
    by_contra h_int
    have h_int_eq : interior (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp h_int
    have : (closure (∅ : Set X)).Nonempty := by
      simpa [h_int_eq] using h_closure
    simpa [closure_empty] using this
  · intro h_int
    rcases h_int with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩

theorem closure_interior_closure_interior_triple_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (A : Set X))))))) =
      closure (interior (closure (A : Set X))) := by
  simpa using
    (closure_interior_closure_interior_double_idempotent
      (A := closure (A : Set X)))

theorem interior_closure_interior_triple_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
      interior (closure (interior (A : Set X))) := by
  -- Apply the double idempotent lemma to `closure (interior A)`.
  have h₁ :=
    interior_closure_interior_double_idempotent
      (A := closure (interior (A : Set X)))
  -- Simplify the right‐hand side of `h₁` using the basic idempotent lemma.
  have h₂ :=
    interior_closure_interior_idempotent (A := A)
  simpa [h₂] using h₁

theorem closure_inter_eq_empty_of_disjoint_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X}
    (h : closure (A : Set X) ∩ closure (B : Set X) = (∅ : Set X)) :
    closure ((A ∩ B) : Set X) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : (x : X) ∈ closure (A : Set X) ∩ closure (B : Set X) :=
      (closure_inter_subset_inter_closures (A := A) (B := B)) hx
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [h] using hx'
    exact this
  · exact Set.empty_subset _

theorem Topology.P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalences under the openness assumption.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P3 A ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  -- Combine the equivalences to obtain the desired statement.
  constructor
  · intro hP3
    have hP2 : Topology.P2 A := (h₂.mp) hP3
    have hP1 : Topology.P1 A := (h₁.mpr) hP2
    exact And.intro hP1 hP2
  · rintro ⟨_, hP2⟩
    exact (h₂.mpr) hP2

theorem interior_inter_closure_diff_interior_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ (closure (A : Set X) \ interior (A : Set X)) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxInt, ⟨_, hxNotInt⟩⟩
    exact (hxNotInt hxInt).elim
  · exact Set.empty_subset _

theorem interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ closure (A : Set X) = interior (A : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx
    exact And.intro hx (interior_subset_closure_self (A := A) hx)

theorem interior_inter_closure_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ closure (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxInt, hxCl⟩
    have hContr : False := by
      -- From `x ∈ closure (Aᶜ)` we obtain that every open neighbourhood of `x`
      -- meets `Aᶜ`. In particular, this holds for `interior A`, which is an
      -- open neighbourhood of `x`.
      have hNonempty :
          ((interior (A : Set X)) ∩ (Aᶜ : Set X)).Nonempty :=
        (mem_closure_iff.1 hxCl) (interior (A : Set X)) isOpen_interior hxInt
      rcases hNonempty with ⟨y, ⟨hyInt, hyCompl⟩⟩
      -- But `y ∈ interior A` implies `y ∈ A`, contradicting `y ∈ Aᶜ`.
      have hInA : (y : X) ∈ (A : Set X) := interior_subset hyInt
      exact (hyCompl hInA)
    cases hContr
  · exact Set.empty_subset _

theorem closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxCl, hxInt⟩
    -- We derive a contradiction, showing that the intersection is empty.
    have hContr : False := by
      -- Since `x` is in the closure of `A`, every open neighborhood of `x`
      -- meets `A`. In particular, this holds for `interior (Aᶜ)`.
      have hNonempty :
          ((interior (Aᶜ : Set X)) ∩ (A : Set X)).Nonempty := by
        have h :=
          (mem_closure_iff.1 hxCl) (interior (Aᶜ : Set X)) isOpen_interior hxInt
        -- Reorder the intersection to match the desired form.
        simpa [Set.inter_comm] using h
      rcases hNonempty with ⟨y, ⟨hyIntCompl, hyA⟩⟩
      -- But `y ∈ interior (Aᶜ)` implies `y ∈ Aᶜ`, contradicting `y ∈ A`.
      have : (y : X) ∈ (Aᶜ : Set X) := interior_subset hyIntCompl
      exact (this hyA).elim
    cases hContr
  · exact Set.empty_subset _

theorem closureInterior_diff_interior_subset_boundary {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A : Set X)) \ interior (A : Set X) ⊆
      closure (A : Set X) \ interior (A : Set X) := by
  intro x hx
  rcases hx with ⟨hx_clInt, hx_notInt⟩
  have hx_clA : (x : X) ∈ closure (A : Set X) :=
    (closure_interior_subset_closure (A := A)) hx_clInt
  exact And.intro hx_clA hx_notInt

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X).Nonempty →
      Topology.P1 (A : Set X) →
      (interior (closure (A : Set X))).Nonempty := by
  intro hA hP1
  -- Obtain a point in `interior A` using the existing lemma.
  have hIntA : (interior (A : Set X)).Nonempty :=
    interior_nonempty_of_P1 (A := A) hA hP1
  rcases hIntA with ⟨x, hx_intA⟩
  -- `interior A` is contained in `interior (closure A)`.
  have hx_intCl : (x : X) ∈ interior (closure (A : Set X)) := by
    have h_subset :
        interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_subset_interior_closure (A := A)
    exact h_subset hx_intA
  exact ⟨x, hx_intCl⟩

theorem closure_subset_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro hP2
  have hEq := closure_eq_closure_interior_of_P2 (A := A) hP2
  simpa [hEq] using
    (subset_rfl : closure (A : Set X) ⊆ closure (A : Set X))

theorem closure_compl_eq_complement_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ := by
  -- First inclusion: `closure (Aᶜ) ⊆ (interior A)ᶜ`.
  have h₁ : closure ((Aᶜ) : Set X) ⊆ (interior (A : Set X))ᶜ := by
    -- Since `Aᶜ ⊆ (interior A)ᶜ` and the right–hand side is closed,
    -- the claim follows from `closure_minimal`.
    have h_subset : ((Aᶜ) : Set X) ⊆ (interior (A : Set X))ᶜ := by
      intro x hxAcomp
      intro hxInt
      have hxA : (x : X) ∈ (A : Set X) := interior_subset hxInt
      exact hxAcomp hxA
    have h_closed : IsClosed ((interior (A : Set X))ᶜ) :=
      (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
    exact closure_minimal h_subset h_closed
  -- Second inclusion: `(interior A)ᶜ ⊆ closure (Aᶜ)`.
  have h₂ : (interior (A : Set X))ᶜ ⊆ closure ((Aᶜ) : Set X) := by
    intro x hxNotInt
    by_contra hxNotCl
    -- The open neighbourhood `U := (closure (Aᶜ))ᶜ` contains `x`.
    have hxU : (x : X) ∈ ((closure ((Aᶜ) : Set X))ᶜ) := hxNotCl
    have hU_open : IsOpen ((closure ((Aᶜ) : Set X))ᶜ) :=
      (isClosed_closure : IsClosed (closure ((Aᶜ) : Set X))).isOpen_compl
    -- Show that `U ⊆ A`.
    have hU_subset : ((closure ((Aᶜ) : Set X))ᶜ : Set X) ⊆ (A : Set X) := by
      intro y hy
      by_cases hYA : (y : X) ∈ (A : Set X)
      · exact hYA
      · -- Then `y ∈ Aᶜ`, hence `y ∈ closure (Aᶜ)`, contradicting `hy`.
        have hyComp : (y : X) ∈ ((Aᶜ) : Set X) := by
          simpa using hYA
        have hyCl : (y : X) ∈ closure ((Aᶜ) : Set X) := subset_closure hyComp
        have : (y : X) ∈ ((closure ((Aᶜ) : Set X))ᶜ) := hy
        exact (this hyCl).elim
    -- The point `x` is in the interior of `A`, contradicting `hxNotInt`.
    have hxIntA : (x : X) ∈ interior (A : Set X) := by
      have hxIntU :
          (x : X) ∈ interior ((closure ((Aᶜ) : Set X))ᶜ : Set X) := by
        simpa [hU_open.interior_eq] using hxU
      have hIntSubset :
          interior ((closure ((Aᶜ) : Set X))ᶜ : Set X) ⊆ interior (A : Set X) :=
        interior_mono hU_subset
      exact hIntSubset hxIntU
    exact hxNotInt hxIntA
  -- Combine the two inclusions for the desired equality.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.P3_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 A ↔ interior (A : Set X) = A := by
  constructor
  · intro hP3
    exact interior_eq_self_of_isClosed_and_P3 (A := A) hA_closed hP3
  · intro hIntEq
    have hOpen : IsOpen (A : Set X) := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using this
    simpa using Topology.P3_of_isOpen (A := A) hOpen

theorem P2_inter_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hA_P2 : Topology.P2 (A : Set X)) (hB_P2 : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- A and B are closed and satisfy `P2`, hence they are open.
  have hA_open : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P2 (A := A) hA_closed hA_P2
  have hB_open : IsOpen (B : Set X) :=
    isOpen_of_isClosed_and_P2 (A := B) hB_closed hB_P2
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B : Set X) := hA_open.inter hB_open
  -- An open set automatically satisfies `P2`.
  simpa using Topology.P2_of_isOpen (A := A ∩ B) hOpen

theorem interior_closure_interior_eq_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (closure (interior (A : Set X))) = interior (closure (A : Set X)) := by
  have h := closure_interior_eq_closure_of_isOpen (A := A) hA
  simpa [h]

theorem closure_union_eq_union_closure_left_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed (A : Set X)) :
    closure ((A ∪ B) : Set X) = A ∪ closure (B : Set X) := by
  have h := closure_union_eq_union_closure (A := A) (B := B)
  simpa [hA.closure_eq] using h

theorem interior_closure_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X)) ⊆
      closure (interior (closure (A : Set X))) := by
  intro x hx
  exact subset_closure hx

theorem closure_union_eq_union_closure_right_of_isClosed {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hB : IsClosed (B : Set X)) :
    closure ((A ∪ B) : Set X) = closure (A : Set X) ∪ B := by
  have h := closure_union_eq_union_closure (A := A) (B := B)
  simpa [hB.closure_eq] using h

theorem isClosed_interior_iff_closure_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed (interior (A : Set X)) ↔
      closure (interior (A : Set X)) = interior (A : Set X) := by
  constructor
  · intro hClosed
    simpa [hClosed.closure_eq]
  · intro hEq
    have hClosed_closure : IsClosed (closure (interior (A : Set X))) := isClosed_closure
    simpa [hEq] using hClosed_closure

theorem closure_interior_iInter_subset_iInter_closure_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort _} (f : ι → Set X) :
    closure (interior (⋂ i, f i : Set X)) ⊆ ⋂ i, closure (interior (f i : Set X)) := by
  intro x hx
  -- We prove that `x` belongs to each `closure (interior (f i))`.
  apply Set.mem_iInter.2
  intro i
  -- Use monotonicity of `interior` to obtain the required inclusion.
  have hSubset : interior (⋂ i, f i : Set X) ⊆ interior (f i : Set X) := by
    apply interior_mono
    exact Set.iInter_subset _ i
  -- Apply `closure_mono` to transfer membership through the closure.
  exact (closure_mono hSubset) hx

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = s := by
  ext x
  simp

theorem nonempty_of_closure_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (interior (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro h_closure
  -- First, obtain non‐emptiness of `interior A` from that of its closure.
  have h_int : (interior (A : Set X)).Nonempty :=
    (closure_interior_nonempty_iff_interior_nonempty (A := A)).1 h_closure
  -- Any point of `interior A` is, a fortiori, a point of `A`.
  rcases h_int with ⟨x, hx_int⟩
  exact ⟨x, interior_subset hx_int⟩

theorem P3_union_dense {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : closure (A : Set X) = (Set.univ : Set X))
    (hB : closure (B : Set X) = (Set.univ : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- First, observe that `A ∪ B` is dense.
  have hDenseUnion : closure ((A ∪ B) : Set X) = (Set.univ : Set X) := by
    have h := closure_union_eq_union_closure (A := A) (B := B)
    simpa [hA, hB, Set.union_univ, Set.univ_union] using h
  -- A dense set satisfies `P3`.
  exact Topology.P3_of_dense (A := A ∪ B) hDenseUnion

theorem interior_iUnion_subset_interior_iUnion {X : Type*} [TopologicalSpace X]
    {ι : Sort _} (f : ι → Set X) :
    (⋃ i, interior (f i : Set X)) ⊆ interior (⋃ i, f i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_int⟩
  have h_subset :
      interior (f i : Set X) ⊆ interior (⋃ j, f j : Set X) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  exact h_subset hx_int

theorem isClosed_eq_univ_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) → A = (Set.univ : Set X) := by
  intro hDense
  simpa [hA_closed.closure_eq] using hDense

theorem closure_interior_closure_eq_closure_interior_of_P2 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (interior (closure (A : Set X))) =
        closure (interior (A : Set X)) := by
  intro hP2
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  exact closure_interior_closure_eq_closure_interior_of_P1 (A := A) hP1

theorem interior_complement_eq_complement_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior ((Aᶜ) : Set X) = (closure (A : Set X))ᶜ := by
  -- Apply the existing lemma to the complement of `A`
  have h : closure (A : Set X) = (interior ((Aᶜ) : Set X))ᶜ := by
    simpa [Set.compl_compl] using
      (closure_compl_eq_complement_interior (A := (Aᶜ : Set X)))
  -- Take complements of both sides to obtain the desired equality
  have h' : interior ((Aᶜ) : Set X) = (closure (A : Set X))ᶜ := by
    have := congrArg Set.compl h
    simpa [Set.compl_compl] using this.symm
  exact h'

theorem interior_closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) ∩ interior ((Aᶜ) : Set X) = (∅ : Set X) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxIntCl, hxIntCompl⟩
    have h_mem_closure : (x : X) ∈ closure (A : Set X) :=
      interior_subset hxIntCl
    -- Using `interior (Aᶜ) = (closure A)ᶜ`
    have h_not_mem_closure : (x : X) ∈ (closure (A : Set X))ᶜ := by
      have h_eq :=
        interior_complement_eq_complement_closure (A := A)
      simpa [h_eq] using hxIntCompl
    have hFalse : False := h_not_mem_closure h_mem_closure
    cases hFalse
  · exact Set.empty_subset _

theorem P2_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P2 (closure A) := by
  intro hOpen
  have h := (P2_closure_iff_isOpen_closure (A := A)).mpr hOpen
  simpa using h

theorem clopen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    IsClosed (A : Set X) ∧ IsOpen (A : Set X) := by
  exact ⟨hA_closed, isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2⟩

theorem interior_closure_complement_eq_complement_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure ((Aᶜ) : Set X)) =
      (closure (interior (A : Set X)))ᶜ := by
  have h₁ :
      closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ := by
    simpa using
      (closure_complement_eq_complement_interior (A := A))
  have h₂ :
      interior ((interior (A : Set X))ᶜ) =
        (closure (interior (A : Set X)))ᶜ := by
    simpa using
      (interior_complement_eq_complement_closure
        (A := interior (A : Set X)))
  simpa [h₁] using h₂

theorem P3_inter_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hA_P3 : Topology.P3 (A : Set X)) (hB_P3 : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- From `P3` and closedness, both `A` and `B` are open.
  have hA_open : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P3 (A := A) hA_closed hA_P3
  have hB_open : IsOpen (B : Set X) :=
    isOpen_of_isClosed_and_P3 (A := B) hB_closed hB_P3
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B : Set X) := hA_open.inter hB_open
  -- Any open set satisfies `P3`.
  simpa using Topology.P3_of_isOpen (A := A ∩ B) hOpen

theorem isClosed_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X))) := by
  -- The closure of any set is closed.
  simpa using
    (isClosed_closure : IsClosed (closure (interior (A : Set X))))

theorem interior_closure_union_closure_complement {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) ∪ closure ((Aᶜ) : Set X) =
      (Set.univ : Set X) := by
  classical
  -- A handy rewriting of `closure (Aᶜ)`.
  have hEq : closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ :=
    closure_compl_eq_complement_interior (A := A)
  -- Prove the equality by double inclusion.
  apply Set.Subset.antisymm
  · intro x _; exact Set.mem_univ x
  · intro x _
    by_cases hInt : (x : X) ∈ interior (A : Set X)
    · -- `x ∈ interior A` ⇒ `x ∈ interior (closure A)`.
      have hIncl : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
        interior_subset_interior_closure (A := A)
      exact Or.inl (hIncl hInt)
    · -- Otherwise, `x ∈ (interior A)ᶜ = closure (Aᶜ)`.
      have hxCompl : (x : X) ∈ (interior (A : Set X))ᶜ := by
        simp [hInt]
      have hxCl : (x : X) ∈ closure ((Aᶜ) : Set X) := by
        simpa [hEq] using hxCompl
      exact Or.inr hxCl

theorem P1_P2_P3_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  simpa using (Topology.P1_P2_P3_of_isOpen (A := A) hOpen)

theorem interior_union_closure_complement {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ closure ((Aᶜ) : Set X) = (Set.univ : Set X) := by
  classical
  -- We prove the equality by showing mutual inclusion.
  apply Set.Subset.antisymm
  · -- The union is obviously contained in `univ`.
    intro x hx
    cases hx with
    | inl _ => exact Set.mem_univ _
    | inr _ => exact Set.mem_univ _
  · -- Conversely, every point of `univ` belongs to the union.
    intro x _
    by_cases hx : (x : X) ∈ interior (A : Set X)
    · -- If `x ∈ interior A`, we are done.
      exact Or.inl hx
    · -- Otherwise, use `closure (Aᶜ) = (interior A)ᶜ`.
      have hEq := closure_compl_eq_complement_interior (A := A)
      have : (x : X) ∈ closure ((Aᶜ) : Set X) := by
        have : (x : X) ∈ (interior (A : Set X))ᶜ := by
          simp [hx]
        simpa [hEq] using this
      exact Or.inr this

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) ↔
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
  constructor
  · intro hP1
    exact closure_subset_closure_interior_of_P1 (A := A) hP1
  · intro hSub
    -- The reverse inclusion is always true.
    have hSup : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset (s := A))
    -- Hence we have equality of the two closures.
    have hEq : closure (A : Set X) = closure (interior (A : Set X)) :=
      Set.Subset.antisymm hSub hSup
    -- Use the existing equivalence with this equality.
    have hP1 :=
      (P1_iff_closure_eq_closure_interior (A := A)).mpr hEq
    exact hP1

theorem closure_interior_closure_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hP1
  -- `closure A = closure (interior A)` by `P1`
  have h₁ := closure_eq_closure_interior_of_P1 (A := A) hP1
  -- `closure (interior (closure A)) = closure (interior A)` by `P1`
  have h₂ := closure_interior_closure_eq_closure_interior_of_P1 (A := A) hP1
  calc
    closure (interior (closure (A : Set X)))
        = closure (interior (A : Set X)) := by
          simpa using h₂
    _ = closure (A : Set X) := by
          simpa using h₁.symm

theorem closure_inter_interiors_subset_closure_interior_inter {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior ((A ∩ B) : Set X)) := by
  apply closure_mono
  exact inter_interiors_subset_interior_inter (A := A) (B := B)

theorem isClosed_closure_diff_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    IsClosed (closure (A : Set X) \ A) := by
  -- Rewrite the set as an intersection of two closed sets.
  have h_eq : (closure (A : Set X) \ A) = closure (A : Set X) ∩ (Aᶜ : Set X) := rfl
  -- Both `closure A` and `Aᶜ` are closed.
  have h_closed₁ : IsClosed (closure (A : Set X)) := isClosed_closure
  have h_closed₂ : IsClosed ((Aᶜ) : Set X) := hA.isClosed_compl
  -- The intersection of closed sets is closed.
  simpa [h_eq] using h_closed₁.inter h_closed₂

theorem boundary_eq_closure_inter_closure_compl {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ interior (A : Set X) =
      closure (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
  classical
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- First inclusion: from left to right.
    intro x hx
    rcases hx with ⟨hx_clA, hx_notInt⟩
    -- `x` already belongs to `closure A`.
    have hx_clAc : (x : X) ∈ closure ((Aᶜ) : Set X) := by
      -- Use the identity `closure (Aᶜ) = (interior A)ᶜ`.
      have h_eq := closure_compl_eq_complement_interior (A := A)
      -- Since `x ∉ interior A`, we have `x ∈ (interior A)ᶜ`.
      have : (x : X) ∈ (interior (A : Set X))ᶜ := hx_notInt
      simpa [h_eq] using this
    exact And.intro hx_clA hx_clAc
  · -- Second inclusion: from right to left.
    intro x hx
    rcases hx with ⟨hx_clA, hx_clAc⟩
    -- Translate membership in `closure (Aᶜ)` to non-membership in `interior A`.
    have hx_notInt : (x : X) ∉ interior (A : Set X) := by
      -- Via `closure (Aᶜ) = (interior A)ᶜ`.
      have h_eq := closure_compl_eq_complement_interior (A := A)
      have : (x : X) ∈ (interior (A : Set X))ᶜ := by
        simpa [h_eq] using hx_clAc
      exact this
    exact And.intro hx_clA hx_notInt

theorem P1_and_P3_of_closure_eq_interior_fixed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) = interior (A : Set X) →
      (Topology.P1 A ∧ Topology.P3 A) := by
  intro hEq
  -- First, prove P1.
  have hP1 : Topology.P1 (A : Set X) := by
    dsimp [Topology.P1]
    intro x hxA
    -- From `x ∈ A`, we get `x ∈ closure A`.
    have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    -- Using the hypothesis, `closure A = interior A`, hence `x ∈ interior A`.
    have hx_int : (x : X) ∈ interior (A : Set X) := by
      simpa [hEq] using hx_closure
    -- Finally, `interior A ⊆ closure (interior A)` by `subset_closure`.
    exact subset_closure hx_int
  -- Next, prove P3.
  have hP3 : Topology.P3 (A : Set X) := by
    dsimp [Topology.P3]
    intro x hxA
    -- As above, `x ∈ closure A`.
    have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    -- Convert this to membership in `interior A` via the hypothesis.
    have hx_int : (x : X) ∈ interior (A : Set X) := by
      simpa [hEq] using hx_closure
    -- Monotonicity of `interior` yields `interior A ⊆ interior (closure A)`.
    have h_sub :
        interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
    exact h_sub hx_int
  exact And.intro hP1 hP3

theorem P2_union_interiors {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P2 (interior (A : Set X) ∪ interior (B : Set X)) := by
  have hA : Topology.P2 (interior (A : Set X)) :=
    P2_interior (A := A)
  have hB : Topology.P2 (interior (B : Set X)) :=
    P2_interior (A := B)
  simpa using
    (P2_union
      (A := interior (A : Set X))
      (B := interior (B : Set X))
      hA hB)

theorem closure_union_closure_complement {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ closure ((Aᶜ) : Set X) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro x _; exact Set.mem_univ x
  · intro x _
    classical
    by_cases h : (x : X) ∈ closure (A : Set X)
    · exact Or.inl h
    · have h_not_int : (x : X) ∉ interior (A : Set X) := by
        intro hx_int
        have hx_cl : (x : X) ∈ closure (A : Set X) :=
          (interior_subset_closure_self (A := A)) hx_int
        exact h hx_cl
      -- `closure (Aᶜ) = (interior A)ᶜ`
      have h_eq := closure_compl_eq_complement_interior (A := A)
      have hx_cl_compl : (x : X) ∈ closure ((Aᶜ) : Set X) := by
        have : (x : X) ∈ (interior (A : Set X))ᶜ := h_not_int
        simpa [h_eq] using this
      exact Or.inr hx_cl_compl

theorem boundary_eq_boundary_complement {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ interior (A : Set X) =
      closure ((Aᶜ) : Set X) \ interior ((Aᶜ) : Set X) := by
  classical
  -- Boundary of `A` described as an intersection of closures.
  have h₁ :=
    boundary_eq_closure_inter_closure_compl (A := A)
  -- Boundary of `Aᶜ` described similarly, then simplified.
  have h₂ :
      closure ((Aᶜ) : Set X) \ interior ((Aᶜ) : Set X) =
        closure ((Aᶜ) : Set X) ∩ closure (A : Set X) := by
    simpa [Set.compl_compl] using
      (boundary_eq_closure_inter_closure_compl
        (A := (Aᶜ : Set X)))
  -- Compare the two characterisations.
  calc
    closure (A : Set X) \ interior (A : Set X)
        = closure (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
          simpa using h₁
    _ = closure ((Aᶜ) : Set X) ∩ closure (A : Set X) := by
          simpa [Set.inter_comm]
    _ = closure ((Aᶜ) : Set X) \ interior ((Aᶜ) : Set X) := by
          simpa using h₂.symm

theorem boundary_eq_empty_of_isClopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
  have hClosure : closure (A : Set X) = A := hClosed.closure_eq
  have hInterior : interior (A : Set X) = A := hOpen.interior_eq
  simpa [hClosure, hInterior, Set.diff_self]

theorem Topology.P2_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ interior (A : Set X) = A := by
  -- First, translate `P2` into the openness of `A` using an existing lemma.
  have h₁ := Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed
  -- Next, relate the openness of `A` to the equality `interior A = A`.
  have h₂ : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hIntEq
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using this
  -- Combine the two equivalences.
  simpa using h₁.trans h₂

theorem boundary_union_subset_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∪ B) : Set X) \ interior ((A ∪ B) : Set X) ⊆
      (closure (A : Set X) \ interior (A : Set X)) ∪
        (closure (B : Set X) \ interior (B : Set X)) := by
  intro x hx
  rcases hx with ⟨hxClUnion, hxNotIntUnion⟩
  -- Use the description of `closure (A ∪ B)` as the union of the closures.
  have hClEq : closure ((A ∪ B) : Set X) =
      closure (A : Set X) ∪ closure (B : Set X) :=
    closure_union_eq_union_closure (A := A) (B := B)
  have hxCl : (x : X) ∈ closure (A : Set X) ∪ closure (B : Set X) := by
    simpa [hClEq] using hxClUnion
  -- Show that `x` is not in the interior of `A` nor in that of `B`.
  have hxNotIntA : (x : X) ∉ interior (A : Set X) := by
    intro hxIntA
    have hSubset : (A : Set X) ⊆ (A ∪ B) := by
      intro y hy; exact Or.inl hy
    have hxIntUnion :
        (x : X) ∈ interior ((A ∪ B) : Set X) :=
      (interior_mono hSubset) hxIntA
    exact hxNotIntUnion hxIntUnion
  have hxNotIntB : (x : X) ∉ interior (B : Set X) := by
    intro hxIntB
    have hSubset : (B : Set X) ⊆ (A ∪ B) := by
      intro y hy; exact Or.inr hy
    have hxIntUnion :
        (x : X) ∈ interior ((A ∪ B) : Set X) :=
      (interior_mono hSubset) hxIntB
    exact hxNotIntUnion hxIntUnion
  -- Finally, place `x` in the appropriate boundary.
  cases hxCl with
  | inl hxClA =>
      exact Or.inl ⟨hxClA, hxNotIntA⟩
  | inr hxClB =>
      exact Or.inr ⟨hxClB, hxNotIntB⟩

theorem boundary_inter_subset_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) \ interior ((A ∩ B) : Set X) ⊆
      (closure (A : Set X) \ interior (A : Set X)) ∪
        (closure (B : Set X) \ interior (B : Set X)) := by
  classical
  intro x hx
  rcases hx with ⟨hClAB, hNotIntAB⟩
  -- `x` is in the closures of both `A` and `B`
  have hClA : (x : X) ∈ closure (A : Set X) := by
    have hSub : closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
      apply closure_mono; exact Set.inter_subset_left
    exact hSub hClAB
  have hClB : (x : X) ∈ closure (B : Set X) := by
    have hSub : closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
      apply closure_mono; exact Set.inter_subset_right
    exact hSub hClAB
  -- Case distinction on membership in the interiors of `A` and `B`
  by_cases hIntA : (x : X) ∈ interior (A : Set X)
  · by_cases hIntB : (x : X) ∈ interior (B : Set X)
    · -- If `x` is in both interiors, then it lies in the interior of `A ∩ B`,
      -- contradicting `hNotIntAB`.
      have hOpen : IsOpen (interior (A : Set X) ∩ interior (B : Set X)) :=
        isOpen_interior.inter isOpen_interior
      have hxIn : (x : X) ∈ interior (A : Set X) ∩ interior (B : Set X) :=
        And.intro hIntA hIntB
      have hxIntOpen : (x : X) ∈ interior (interior (A : Set X) ∩ interior (B : Set X)) := by
        simpa [hOpen.interior_eq] using hxIn
      have hSubset :
          interior (A : Set X) ∩ interior (B : Set X) ⊆ (A ∩ B : Set X) := by
        intro y hy; exact And.intro (interior_subset hy.1) (interior_subset hy.2)
      have : (x : X) ∈ interior ((A ∩ B) : Set X) :=
        (interior_mono hSubset) hxIntOpen
      exact (hNotIntAB this).elim
    · -- `x ∉ interior B` ⇒ `x` is on the boundary of `B`
      exact Or.inr ⟨hClB, hIntB⟩
  · -- `x ∉ interior A` ⇒ `x` is on the boundary of `A`
    exact Or.inl ⟨hClA, hIntA⟩

theorem closure_diff_interior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hx
  exact hx.1

theorem boundary_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (A : Set X) \ A =
      closure (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
  simpa [hA.interior_eq] using
    (boundary_eq_closure_inter_closure_compl (A := A))

theorem boundary_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) = A \ interior (A : Set X) := by
  simpa [hA.closure_eq]



theorem isClosed_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (closure (A : Set X)))) := by
  simpa using
    (isClosed_closure :
      IsClosed (closure (interior (closure (A : Set X)))))

theorem boundary_eq_closure_interior_diff_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (A : Set X) \ interior (A : Set X) =
        closure (interior (A : Set X)) \ interior (A : Set X) := by
  intro hP1
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxCl, hxNotInt⟩
    have h_sub : closure (A : Set X) ⊆ closure (interior (A : Set X)) :=
      closure_subset_closure_interior_of_P1 (A := A) hP1
    exact And.intro (h_sub hxCl) hxNotInt
  · intro x hx
    rcases hx with ⟨hxClInt, hxNotInt⟩
    have h_sub : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_interior_subset_closure (A := A)
    exact And.intro (h_sub hxClInt) hxNotInt

theorem interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      interior (closure (A : Set X)) ⊆ closure (interior (A : Set X)) := by
  intro hP1
  intro x hx
  -- `P1` gives equality of the two closures.
  have hEq := closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Rewrite `hx` using this equality.
  have hx' : (x : X) ∈ interior (closure (interior (A : Set X))) := by
    simpa [hEq] using hx
  -- Use the fact that `interior S ⊆ S`.
  exact (interior_subset (s := closure (interior (A : Set X)))) hx'

theorem boundary_closed {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior (A : Set X)) := by
  simpa using
    (isClosed_closure_diff_interior (A := A))

theorem boundary_eq_empty_iff_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) ↔
      (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  constructor
  · intro hEmpty
    -- `closure A ⊆ interior A`
    have hCl_subset_int : closure (A : Set X) ⊆ interior (A : Set X) := by
      intro x hxCl
      by_cases hInt : (x : X) ∈ interior (A : Set X)
      · exact hInt
      ·
        have hMem : (x : X) ∈ closure (A : Set X) \ interior (A : Set X) :=
          ⟨hxCl, hInt⟩
        have : (x : X) ∈ (∅ : Set X) := by
          simpa [hEmpty] using hMem
        cases this
    -- `interior A ⊆ closure A`
    have hInt_subset_cl : interior (A : Set X) ⊆ closure (A : Set X) := by
      intro x hxInt
      exact subset_closure (interior_subset hxInt)
    -- `closure A = interior A`
    have hCl_eq_int : closure (A : Set X) = interior (A : Set X) :=
      Set.Subset.antisymm hCl_subset_int hInt_subset_cl
    -- `A ⊆ interior A`
    have hA_subset_int : (A : Set X) ⊆ interior (A : Set X) := by
      intro x hxA
      have hxCl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
      exact hCl_subset_int hxCl
    -- `interior A = A`
    have hInt_eq_A : interior (A : Set X) = A :=
      Set.Subset.antisymm interior_subset hA_subset_int
    -- `closure A = A`
    have hCl_eq_A : closure (A : Set X) = A := by
      apply Set.Subset.antisymm
      · intro x hxCl
        have : (x : X) ∈ interior (A : Set X) := hCl_subset_int hxCl
        exact interior_subset this
      · exact subset_closure
    -- `A` is open and closed
    have hOpen : IsOpen (A : Set X) := by
      simpa [hInt_eq_A] using (isOpen_interior : IsOpen (interior (A : Set X)))
    have hClosed : IsClosed (A : Set X) := by
      simpa [hCl_eq_A] using (isClosed_closure : IsClosed (closure (A : Set X)))
    exact And.intro hOpen hClosed
  · intro hClopen
    exact
      (boundary_eq_empty_of_isClopen (A := A) hClopen.1 hClopen.2)

theorem closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) := by
  -- Apply the generic inclusion with `A := closure A`
  have h :
      closure (interior (closure (A : Set X))) ⊆
        closure (closure (A : Set X)) :=
    closure_interior_subset_closure (A := closure (A : Set X))
  simpa [closure_closure] using h

theorem isClopen_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = interior (A : Set X) →
      (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  intro hEq
  -- The boundary of `A` is empty, since `closure A = interior A`.
  have hBoundary :
      closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
    simpa [hEq, Set.diff_self]
  -- Apply the characterisation of clopen sets via empty boundary.
  exact (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary

theorem Topology.nonempty_iff_interior_nonempty_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hA
    exact interior_nonempty_of_P1 (A := A) hA hP1
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩

theorem boundary_eq_empty_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
  -- A closed set satisfying `P3` is open.
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P3 (A := A) hClosed hP3
  -- For a clopen set, the boundary is empty.
  simpa using
    (boundary_eq_empty_of_isClopen (A := A) hOpen hClosed)

theorem closure_complement_eq_complement_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ := by
  simpa using closure_compl_eq_complement_interior (A := A)

theorem boundary_univ_empty {X : Type*} [TopologicalSpace X] :
    closure (Set.univ : Set X) \ interior (Set.univ : Set X) = (∅ : Set X) := by
  simp [closure_univ, interior_univ]

theorem isClosed_closure_union_closure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    IsClosed (closure (A : Set X) ∪ closure (B : Set X)) := by
  exact
    (isClosed_closure : IsClosed (closure (A : Set X))).union
      (isClosed_closure : IsClosed (closure (B : Set X)))

theorem interior_closure_union_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (B : Set X) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hIntClA =>
      -- Case `x ∈ interior (closure A)`
      have h_closure_subset :
          (closure (A : Set X)) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact (interior_mono h_closure_subset) hIntClA
  | inr hIntB =>
      -- Case `x ∈ interior B`
      -- First, `interior B ⊆ interior (A ∪ B)`
      have h_subset₁ : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hx_int_AuB : (x : X) ∈ interior (A ∪ B : Set X) :=
        (interior_mono h_subset₁) hIntB
      -- Next, `interior (A ∪ B) ⊆ interior (closure (A ∪ B))`
      have h_subset₂ :
          (A ∪ B : Set X) ⊆ closure (A ∪ B) := subset_closure
      exact (interior_mono h_subset₂) hx_int_AuB

theorem closure_interior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hP2
  have h₁ :=
    closure_interior_closure_eq_closure_interior_of_P2 (A := A) hP2
  have h₂ := closure_eq_closure_interior_of_P2 (A := A) hP2
  calc
    closure (interior (closure (A : Set X)))
        = closure (interior (A : Set X)) := h₁
    _ = closure (A : Set X) := by
          simpa using h₂.symm

theorem interior_complement_eq_empty_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) →
      interior ((Aᶜ) : Set X) = (∅ : Set X) := by
  intro hDense
  have hEq := interior_complement_eq_complement_closure (A := A)
  simpa [hDense, Set.compl_univ] using hEq

theorem isClosed_closure_interior_diff_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    IsClosed (closure (interior (A : Set X)) \ interior (A : Set X)) := by
  -- Rewrite the set as an intersection of two closed sets.
  have h_eq :
      (closure (interior (A : Set X)) \ interior (A : Set X)) =
        closure (interior (A : Set X)) ∩ (interior (A : Set X))ᶜ := rfl
  -- `closure (interior A)` is closed.
  have h_closed₁ : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- The complement of `interior A` is closed because `interior A` is open.
  have h_closed₂ : IsClosed ((interior (A : Set X))ᶜ) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  -- The intersection of closed sets is closed.
  simpa [h_eq] using h_closed₁.inter h_closed₂

theorem P1_P2_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  have hOpen : IsOpen (∅ : Set X) := isOpen_empty
  simpa using
    (Topology.P1_P2_P3_of_isOpen (A := (∅ : Set X)) hOpen)

theorem subset_interior_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    (A : Set X) ⊆ interior (closure (A : Set X)) := by
  intro x hxA
  -- Since `A` is open, `interior A = A`.
  have hxIntA : (x : X) ∈ interior (A : Set X) := by
    simpa [hA.interior_eq] using hxA
  -- Monotonicity of `interior` gives the desired inclusion.
  have hMono :
      interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hMono hxIntA

theorem interior_closure_eq_of_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) = closure (B : Set X) →
      interior (closure (A : Set X)) = interior (closure (B : Set X)) := by
  intro h
  simpa using congrArg interior h

theorem Topology.P2_iff_boundary_empty_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro hP2
    have hOpen : IsOpen (A : Set X) :=
      isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
    simpa using
      (boundary_eq_empty_of_isClopen (A := A) hOpen hA_closed)
  · intro hBoundary
    have hClopen :=
      (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
    exact Topology.P2_of_isOpen (A := A) hClopen.1

theorem Topology.P1_and_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    (Topology.P1 A ∧ Topology.P3 A) ↔ IsOpen (A : Set X) := by
  constructor
  · intro h
    -- From `P1 ∧ P3` obtain `P2` using the closedness of `A`.
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P2_iff_P1_and_P3_of_isClosed (A := A) hA_closed).2 h
    -- A closed set satisfies `P2` iff it is open.
    exact
      (Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP2
  · intro hOpen
    -- Any open set satisfies `P1` and `P3`.
    have hP1 : Topology.P1 (A : Set X) :=
      Topology.P1_of_isOpen (A := A) hOpen
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P3_of_isOpen (A := A) hOpen
    exact And.intro hP1 hP3

theorem boundary_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) →
      closure (A : Set X) \ interior (A : Set X) =
        (interior (A : Set X))ᶜ := by
  intro hDense
  classical
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxNotInt
    have hxCl : (x : X) ∈ closure (A : Set X) := by
      simpa [hDense] using (Set.mem_univ (x : X))
    exact And.intro hxCl hxNotInt

theorem P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) := by
  exact
    ⟨Topology.P1_univ (X := X),
      Topology.P2_univ (X := X),
      Topology.P3_univ (X := X)⟩

theorem P1_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) →
      Topology.P1 A := by
  intro hBoundary
  -- An empty boundary implies that `A` is both open and closed.
  have hClopen :
      IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  -- Any open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A) hClopen.1

theorem interior_iUnion_eq_iUnion_of_isOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort _} (f : ι → Set X) (h : ∀ i, IsOpen (f i)) :
    interior (⋃ i, f i : Set X) = ⋃ i, f i := by
  have hOpen : IsOpen (⋃ i, f i : Set X) := isOpen_iUnion (λ i => h i)
  simpa [hOpen.interior_eq] using hOpen.interior_eq

theorem Topology.nonempty_iff_interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hA
    exact interior_nonempty_of_P2 (A := A) hA hP2
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩

theorem interior_closure_diff_interior_subset_boundary {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) \ interior (A : Set X) ⊆
      closure (A : Set X) \ interior (A : Set X) := by
  intro x hx
  rcases hx with ⟨hxIntCl, hxNotInt⟩
  have hxCl : (x : X) ∈ closure (A : Set X) :=
    interior_subset (s := closure (A : Set X)) hxIntCl
  exact And.intro hxCl hxNotInt

theorem boundary_of_dense_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X))
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    closure (A : Set X) \ A = ((Aᶜ) : Set X) := by
  -- Start with the general description of the boundary of a dense set.
  have h := boundary_of_dense (A := A) hDense
  -- Since `A` is open, `interior A = A`; rewrite both sides accordingly.
  simpa [hOpen.interior_eq] using h

theorem boundary_eq_closure_interior_diff_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (A : Set X) \ interior (A : Set X) =
        closure (interior (A : Set X)) \ interior (A : Set X) := by
  intro hP2
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  exact boundary_eq_closure_interior_diff_interior_of_P1 (A := A) hP1

theorem boundary_subset_closure_complement {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ interior (A : Set X) ⊆
      closure ((Aᶜ) : Set X) := by
  intro x hx
  -- Identify the boundary with the intersection of the two closures.
  have hEq := boundary_eq_closure_inter_closure_compl (A := A)
  -- Reinterpret `hx` via this equality.
  have hx' :
      (x : X) ∈ closure (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
    simpa [hEq] using hx
  exact hx'.2

theorem interior_closure_eq_self_of_isOpen_and_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  calc
    interior (closure (A : Set X)) = interior (A : Set X) := by
      simpa [hClosed.closure_eq]
    _ = A := by
      simpa [hOpen.interior_eq]

theorem boundary_of_isClosed_eq_inter_closure_complement {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) =
      (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
  have h := boundary_eq_closure_inter_closure_compl (A := A)
  simpa [hA.closure_eq] using h

theorem closure_eq_univ_of_empty_interior_complement
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntEmpty : interior ((Aᶜ) : Set X) = (∅ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  classical
  -- Relate the complement of `closure A` to `interior (Aᶜ)`.
  have hEq : (closure (A : Set X))ᶜ = interior ((Aᶜ) : Set X) :=
    (interior_complement_eq_complement_closure (A := A)).symm
  -- Deduce that the complement of `closure A` is empty.
  have hCompl : (closure (A : Set X))ᶜ = (∅ : Set X) := by
    simpa [hIntEmpty] using hEq
  -- Show that `closure A` contains every point of the space.
  have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    intro x _
    by_contra hx
    have hxInCompl : (x : X) ∈ (closure (A : Set X))ᶜ := hx
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hCompl] using hxInCompl
    exact this.elim
  -- Conclude the desired equality.
  exact Set.Subset.antisymm (Set.subset_univ _) hSub

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (A : Set X) → Topology.P1 (B : Set X) →
      Topology.P1 (closure (A ∪ B : Set X)) := by
  intro hA hB
  have hUnion : Topology.P1 (A ∪ B : Set X) :=
    Topology.P1_union (A := A) (B := B) hA hB
  exact Topology.P1_closure (A := A ∪ B) hUnion

theorem closure_diff_subset_closure_diff_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB_closed : IsClosed (B : Set X)) :
    closure ((A \ B) : Set X) ⊆ closure (A : Set X) \ interior (B : Set X) := by
  intro x hx
  -- First, `x` lies in the closure of `A`,
  -- because `A \ B` is a subset of `A`.
  have hx_clA : (x : X) ∈ closure (A : Set X) := by
    have h_subset : ((A \ B) : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact (closure_mono h_subset) hx
  -- Next, we show that `x` is *not* in `interior B`.
  have hx_notIntB : (x : X) ∉ interior (B : Set X) := by
    intro hxIntB
    -- Since `x` is in the closure of `A \ B`,
    -- every open neighbourhood of `x` meets `A \ B`.
    have h_nonempty :=
      (mem_closure_iff.1 hx) (interior (B : Set X)) isOpen_interior hxIntB
    rcases h_nonempty with ⟨y, ⟨hyIntB, hyDiff⟩⟩
    -- But `interior B ⊆ B`, so `y ∈ B`.
    have hy_inB : (y : X) ∈ B := interior_subset hyIntB
    -- Yet `y ∈ A \ B` gives `y ∉ B`, contradiction.
    exact (hyDiff.2) hy_inB
  exact And.intro hx_clA hx_notIntB

theorem closure_inter_interior_subset_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ∩ interior (B : Set X) ⊆ closure ((A ∩ B) : Set X) := by
  intro x hx
  rcases hx with ⟨hxClA, hxIntB⟩
  -- We verify the defining property of being in the closure of `A ∩ B`.
  have hxClAB : (x : X) ∈ closure ((A ∩ B) : Set X) := by
    -- Use the neighborhood characterization of closure.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighborhood `U ∩ interior B` of `x`.
    have hOpen' : IsOpen (U ∩ interior (B : Set X)) := hUopen.inter isOpen_interior
    have hxU' : (x : X) ∈ U ∩ interior (B : Set X) := by
      exact And.intro hxU hxIntB
    -- Since `x ∈ closure A`, this neighborhood meets `A`.
    have hNonempty :
        ((U ∩ interior (B : Set X)) ∩ (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hxClA _ hOpen' hxU'
    -- Extract a point witnessing the non‐emptiness and show it lies in
    -- `U ∩ (A ∩ B)`.
    rcases hNonempty with ⟨y, ⟨hyU, hyIntB⟩, hyA⟩
    have hyB : (y : X) ∈ (B : Set X) := interior_subset hyIntB
    exact ⟨y, ⟨hyU, And.intro hyA hyB⟩⟩
  exact hxClAB

theorem interior_closure_inter_eq_empty_of_disjoint_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ closure (B : Set X) = (∅ : Set X) →
      interior (closure ((A ∩ B) : Set X)) = (∅ : Set X) := by
  intro hDisjoint
  apply Set.Subset.antisymm
  · intro x hx
    have hx_cl : (x : X) ∈ closure ((A ∩ B) : Set X) :=
      interior_subset hx
    have hx_inter :
        (x : X) ∈ closure (A : Set X) ∩ closure (B : Set X) :=
      (closure_inter_subset_inter_closures (A := A) (B := B)) hx_cl
    simpa [hDisjoint] using hx_inter
  · intro x hx
    cases hx

theorem interior_complement_eq_empty_iff_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior ((Aᶜ) : Set X) = (∅ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  -- A handy rewriting of `interior (Aᶜ)`.
  have hEq : interior ((Aᶜ) : Set X) = (closure (A : Set X))ᶜ :=
    interior_complement_eq_complement_closure (A := A)
  constructor
  · intro hIntEmpty
    -- Convert the assumption using `hEq`.
    have hComplEmpty : (closure (A : Set X))ᶜ = (∅ : Set X) := by
      simpa [hEq] using hIntEmpty
    -- Show that `closure A = univ`.
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _
    -- If `x ∉ closure A`, we get a contradiction with `hComplEmpty`.
    by_cases hx : (x : X) ∈ closure (A : Set X)
    · exact hx
    ·
      have : (x : X) ∈ (closure (A : Set X))ᶜ := hx
      have : (x : X) ∈ (∅ : Set X) := by
        simpa [hComplEmpty] using this
      exact this.elim
  · intro hDense
    -- Rewrite via `hEq` and `hDense`.
    have : interior ((Aᶜ) : Set X) = (Set.univ : Set X)ᶜ := by
      simpa [hDense] using hEq
    simpa [Set.compl_univ] using this

theorem boundary_empty {X : Type*} [TopologicalSpace X] :
    closure (∅ : Set X) \ interior (∅ : Set X) = (∅ : Set X) := by
  simp [closure_empty, interior_empty]

theorem closure_inter_eq_self_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = (A : Set X) ∩ B := by
  simpa using (hA.inter hB).closure_eq

theorem closure_union_closure_right {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (A ∪ closure (B : Set X)) = closure (A ∪ B) := by
  calc
    closure (A ∪ closure (B : Set X))
        = closure (A : Set X) ∪ closure (closure (B : Set X)) := by
          simpa using
            closure_union_eq_union_closure (A := A) (B := closure (B : Set X))
    _ = closure (A : Set X) ∪ closure (B : Set X) := by
          simpa [closure_closure]
    _ = closure (A ∪ B) := by
          simpa using
            (closure_union_eq_union_closure (A := A) (B := B)).symm

theorem subset_of_closure_subset_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : closure (A : Set X) ⊆ interior (B : Set X)) :
    (A : Set X) ⊆ B := by
  intro x hxA
  have hxCl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have hxInt : (x : X) ∈ interior (B : Set X) := h hxCl
  exact interior_subset hxInt

theorem closure_interior_union_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∪ interior (closure (A : Set X)) ⊆
      closure (A : Set X) := by
  intro x hx
  cases hx with
  | inl h_closure_int =>
      have h_subset :
          closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
        closure_interior_subset_closure (A := A)
      exact h_subset h_closure_int
  | inr h_interior_cl =>
      have h : (x : X) ∈ closure (A : Set X) :=
        (interior_subset (s := closure (A : Set X))) h_interior_cl
      exact h

theorem P2_iff_subset_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 A ↔ (A ⊆ interior (closure (A : Set X))) := by
  have h := (Topology.P3_iff_P2_of_isOpen (A := A) hA).symm
  simpa [Topology.P3] using h

theorem P2_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) →
      Topology.P2 (A : Set X) := by
  intro hBoundary
  -- An empty boundary implies that `A` is both open and closed.
  have hClopen :
      IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  -- Every open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A) hClopen.1

theorem interior_inter_closure_subset_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∩ closure (B : Set X) ⊆ closure ((A ∩ B) : Set X) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We show that `x` belongs to the closure of `A ∩ B`
  have h : (x : X) ∈ closure ((A ∩ B) : Set X) := by
    -- Use the neighbourhood characterization of `closure`
    apply (mem_closure_iff).2
    intro U hUopen hxU
    -- Consider the open neighbourhood `U ∩ interior A` of `x`
    have hVopen : IsOpen (U ∩ interior (A : Set X)) := hUopen.inter isOpen_interior
    have hxV : (x : X) ∈ U ∩ interior (A : Set X) := And.intro hxU hxIntA
    -- Since `x ∈ closure B`, this neighbourhood meets `B`
    have hNonempty :
        ((U ∩ interior (A : Set X)) ∩ (B : Set X)).Nonempty :=
      (mem_closure_iff).1 hxClB _ hVopen hxV
    -- Extract a witness in `A ∩ B` that also lies in `U`
    rcases hNonempty with ⟨y, ⟨⟨hyU, hyIntA⟩, hyB⟩⟩
    have hyA : (y : X) ∈ (A : Set X) := interior_subset hyIntA
    exact ⟨y, And.intro hyU (And.intro hyA hyB)⟩
  exact h

theorem clopen_iff_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) ↔
      closure (A : Set X) = interior (A : Set X) := by
  constructor
  · rintro ⟨hOpen, hClosed⟩
    have h₁ : closure (A : Set X) = A := hClosed.closure_eq
    have h₂ : interior (A : Set X) = A := hOpen.interior_eq
    simpa [h₁, h₂]
  · intro hEq
    simpa using isClopen_of_closure_eq_interior (A := A) hEq

theorem boundary_interior_eq_closure_inter_complement
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) \ interior (A : Set X) =
      closure (interior (A : Set X)) ∩
        closure ((interior (A : Set X))ᶜ) := by
  simpa using
    (boundary_of_isOpen (A := interior (A : Set X)) isOpen_interior)

theorem interior_inter_interiors_eq_inter_interiors
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (interior (A : Set X) ∩ interior B) =
      interior (A : Set X) ∩ interior B := by
  have hOpenA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hOpenB : IsOpen (interior (B : Set X)) := isOpen_interior
  simpa using
    (interior_inter_eq_of_isOpen
        (A := interior (A : Set X)) (B := interior (B : Set X))
        hOpenA hOpenB)

theorem P1_P2_P3_union_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa using
    (Topology.P1_P2_P3_of_isOpen (A := (A ∪ B : Set X)) hOpen)

theorem boundary_closure_subset_boundary {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) \ interior (closure (A : Set X)) ⊆
      closure (A : Set X) \ interior (A : Set X) := by
  intro x hx
  rcases hx with ⟨hxCl, hxNotIntCl⟩
  -- If `x` were in `interior A`, then it would also lie in `interior (closure A)`,
  -- contradicting `hxNotIntCl`.
  have hxNotIntA : (x : X) ∉ interior (A : Set X) := by
    intro hxIntA
    have : (x : X) ∈ interior (closure (A : Set X)) := by
      have h_subset :
          interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      exact h_subset hxIntA
    exact hxNotIntCl this
  exact And.intro hxCl hxNotIntA

theorem P3_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) →
      Topology.P3 A := by
  intro hBoundary
  -- From the empty boundary we infer that `A` is both open and closed.
  have hClopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  -- Every open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A) hClopen.1

theorem Topology.P1_P2_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen (A : Set X) := by
  constructor
  · rintro ⟨_, hP2, _⟩
    exact isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  · intro hOpen
    exact Topology.P1_P2_P3_of_isOpen (A := A) hOpen

theorem closure_diff_eq_self_inter_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) \ A = closure (A : Set X) ∩ (A : Set X)ᶜ := by
  rfl

theorem P3_union_interiors {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P3 (interior (A : Set X) ∪ interior B) := by
  have hA : Topology.P3 (interior (A : Set X)) := P3_interior (A := A)
  have hB : Topology.P3 (interior (B : Set X)) := P3_interior (A := B)
  simpa using
    (P3_union
      (A := interior (A : Set X))
      (B := interior (B : Set X))
      hA hB)

theorem interior_subset_interior_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ⊆ interior (A ∪ B) := by
  apply interior_mono
  intro x hx
  exact Or.inl hx

theorem P1_P2_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ∧
      Topology.P2 (interior (A : Set X)) ∧
        Topology.P3 (interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P1_P2_P3_of_isOpen (A := interior (A : Set X)) hOpen)

theorem closure_eq_interior_iff_boundary_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) = interior (A : Set X) ↔
      closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
  classical
  constructor
  · intro hEq
    simpa [hEq, Set.diff_self]
  · intro hEmpty
    apply Set.Subset.antisymm
    · intro x hxCl
      by_cases hxInt : (x : X) ∈ interior (A : Set X)
      · exact hxInt
      ·
        have hxDiff :
            (x : X) ∈ closure (A : Set X) \ interior (A : Set X) :=
          And.intro hxCl hxInt
        have : (x : X) ∈ (∅ : Set X) := by
          simpa [hEmpty] using hxDiff
        cases this
    · intro x hxInt
      exact subset_closure (interior_subset hxInt)

theorem isClosed_iff_closure_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (A : Set X) ↔ closure (A : Set X) = A := by
  constructor
  · intro hA_closed
    simpa using hA_closed.closure_eq
  · intro hEq
    have : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [hEq] using this

theorem interior_closure_interior_eq_interior_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (interior (A : Set X))) = interior (A : Set X) := by
  apply Set.Subset.antisymm
  · -- `interior (closure (interior A)) ⊆ interior A`
    have hsubset₁ :
        closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_interior_subset_closure (A := A)
    have hsubset :
        closure (interior (A : Set X)) ⊆ (A : Set X) := by
      simpa [hA_closed.closure_eq] using hsubset₁
    exact interior_mono hsubset
  · -- `interior A ⊆ interior (closure (interior A))`
    exact interior_subset_interior_closure_interior (A := A)

theorem dense_inter_open_nonempty {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hA : closure (A : Set X) = (Set.univ : Set X))
    (hU : IsOpen (U : Set X)) (hU_nonempty : (U : Set X).Nonempty) :
    ((A ∩ U) : Set X).Nonempty := by
  -- Choose a point `x` in the non-empty open set `U`.
  rcases hU_nonempty with ⟨x, hxU⟩
  -- Since `A` is dense, `x` lies in the closure of `A`.
  have hx_closureA : (x : X) ∈ closure (A : Set X) := by
    simpa [hA] using (Set.mem_univ (x : X))
  -- The neighbourhood characterisation of closure yields
  -- that `U` meets `A`.
  have h_inter : ((U : Set X) ∩ A).Nonempty :=
    (mem_closure_iff.1 hx_closureA) U hU hxU
  -- Reorder the intersection to obtain the required statement.
  simpa [Set.inter_comm] using h_inter

theorem subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 (A : Set X))
    (hB : (B : Set X) ⊆ closure (A : Set X)) :
    (B : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hxB
  have hxClA : (x : X) ∈ closure (A : Set X) := hB hxB
  have hEq : closure (A : Set X) = closure (interior (A : Set X)) :=
    closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [hEq] using hxClA

theorem isClosed_closure_inter_closure {X : Type*} [TopologicalSpace X] (A B : Set X) :
    IsClosed (closure (A : Set X) ∩ closure (B : Set X)) := by
  exact
    (isClosed_closure : IsClosed (closure (A : Set X))).inter
      (isClosed_closure : IsClosed (closure (B : Set X)))

theorem P1_P2_P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) ∧
      Topology.P2 (interior (closure (A : Set X))) ∧
        Topology.P3 (interior (closure (A : Set X))) := by
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa using
    (Topology.P1_P2_P3_of_isOpen
      (A := interior (closure (A : Set X))) hOpen)

theorem P2_union_of_isOpen_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  have hP2A : Topology.P2 (A : Set X) :=
    Topology.P2_of_isOpen (A := A) hA
  exact Topology.P2_union (A := A) (B := B) hP2A hB

theorem closure_union_closure_left {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure (closure (A : Set X) ∪ B) = closure (A ∪ B) := by
  calc
    closure (closure (A : Set X) ∪ B)
        = closure (closure (A : Set X)) ∪ closure (B : Set X) := by
          simpa using
            closure_union_eq_union_closure
              (A := closure (A : Set X)) (B := B)
    _ = closure (A : Set X) ∪ closure (B : Set X) := by
          simpa [closure_closure]
    _ = closure (A ∪ B : Set X) := by
          simpa using
            (closure_union_eq_union_closure (A := A) (B := B)).symm

theorem closure_union_closure_closure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (closure (A : Set X) ∪ closure (B : Set X)) =
      closure (A ∪ B) := by
  calc
    closure (closure (A : Set X) ∪ closure (B : Set X))
        = closure (A ∪ closure (B : Set X)) := by
          simpa using
            closure_union_closure_left (A := A) (B := closure (B : Set X))
    _ = closure (A ∪ B) := by
          simpa using
            closure_union_closure_right (A := A) (B := B)



theorem P3_union_of_isOpen_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- An open set automatically satisfies `P3`.
  have hP3A : Topology.P3 (A : Set X) :=
    Topology.P3_of_isOpen (A := A) hA
  -- The union of two sets satisfying `P3` again satisfies `P3`.
  exact Topology.P3_union (A := A) (B := B) hP3A hB

theorem closure_interior_closure_eq_closure_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (interior (closure (A : Set X))) =
      closure (interior (A : Set X)) := by
  simpa [hA_closed.closure_eq]



theorem boundary_interior_subset_boundary {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A : Set X)) \ interior (A : Set X) ⊆
      closure (A : Set X) \ interior (A : Set X) := by
  intro x hx
  rcases hx with ⟨hxClInt, hxNotIntA⟩
  have hxClA : (x : X) ∈ closure (A : Set X) :=
    (closure_interior_subset_closure (A := A)) hxClInt
  exact And.intro hxClA hxNotIntA

theorem nonempty_iff_interior_closure_nonempty_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (closure (A : Set X))).Nonempty := by
  classical
  constructor
  · intro hA
    exact
      interior_closure_nonempty_of_P3 (A := A) hA hP3
  · intro hIntCl
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · -- Derive a contradiction from `hIntCl` and `hA = ∅`.
      have hA_eq : (A : Set X) = (∅ : Set X) :=
        Set.not_nonempty_iff_eq_empty.mp hA
      have hIntEmpty :
          interior (closure (A : Set X)) = (∅ : Set X) := by
        simpa [hA_eq, closure_empty, interior_empty]
      rcases hIntCl with ⟨x, hx⟩
      have : (x : X) ∈ (∅ : Set X) := by
        simpa [hIntEmpty] using hx
      cases this

theorem closure_interior_union_closure_complement {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A : Set X)) ∪ closure ((Aᶜ) : Set X) =
      (Set.univ : Set X) := by
  classical
  apply Set.Subset.antisymm
  · -- `closure (interior A) ∪ closure (Aᶜ) ⊆ univ`
    intro x _
    exact Set.mem_univ x
  · -- `univ ⊆ closure (interior A) ∪ closure (Aᶜ)`
    intro x _
    by_cases hInt : (x : X) ∈ interior (A : Set X)
    · -- Case `x ∈ interior A`
      have hx : (x : X) ∈ closure (interior (A : Set X)) :=
        subset_closure hInt
      exact Or.inl hx
    · -- Case `x ∉ interior A`
      have hEq :
          closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ :=
        closure_compl_eq_complement_interior (A := A)
      have hx : (x : X) ∈ closure ((Aᶜ) : Set X) := by
        have : (x : X) ∈ (interior (A : Set X))ᶜ := hInt
        simpa [hEq] using this
      exact Or.inr hx

theorem isOpen_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
  constructor
  · intro hOpen
    exact hOpen.interior_eq
  · intro hEq
    have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [hEq] using hOpenInt

theorem interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B) := by
  intro x hxB
  -- `interior` is monotone with respect to set inclusion.
  have h_subset : (B : Set X) ⊆ (A ∪ B : Set X) := by
    intro y hy
    exact Or.inr hy
  exact (interior_mono h_subset) hxB

theorem inter_interiors_subset_interior_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∩ interior B ⊆
      interior (closure ((A ∩ B) : Set X)) := by
  intro x hx
  -- First, `x` belongs to `interior (A ∩ B)`.
  have hx_int : (x : X) ∈ interior ((A ∩ B) : Set X) :=
    inter_interiors_subset_interior_inter (A := A) (B := B) hx
  -- Then use the inclusion `interior S ⊆ interior (closure S)`.
  have h_subset :
      interior ((A ∩ B) : Set X) ⊆
        interior (closure ((A ∩ B) : Set X)) :=
    interior_subset_interior_closure (A := A ∩ B)
  exact h_subset hx_int

theorem isOpen_of_isClosed_and_boundary_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X))
    (hBoundary : closure (A : Set X) \ interior (A : Set X) = (∅ : Set X)) :
    IsOpen (A : Set X) := by
  have hClopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  exact hClopen.1

theorem closure_diff_closure_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) \ closure (B : Set X) ⊆ closure ((A \ B) : Set X) := by
  intro x hx
  rcases hx with ⟨hClA, hNotClB⟩
  -- We prove that `x` lies in the closure of `A \ B`.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- Consider the open neighbourhood `U ∩ (closure B)ᶜ` of `x`,
  -- which is disjoint from `B`.
  let V : Set X := U ∩ (closure (B : Set X))ᶜ
  have hVopen : IsOpen V := hUopen.inter (isClosed_closure.isOpen_compl)
  have hxV : (x : X) ∈ V := And.intro hxU hNotClB
  -- Since `x ∈ closure A`, this open set meets `A`.
  obtain ⟨y, ⟨hyU, hyComplB⟩, hyA⟩ :=
    (mem_closure_iff).1 hClA V hVopen hxV
  -- The point `y` is in `U`, in `A`, and not in `B`.
  have hyNotB : (y : X) ∉ (B : Set X) := by
    intro hYB
    have : (y : X) ∈ closure (B : Set X) := subset_closure hYB
    exact hyComplB this
  -- Hence `y` witnesses that `U` meets `A \ B`.
  exact ⟨y, And.intro hyU (And.intro hyA hyNotB)⟩

theorem closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∪ interior (A : Set X) = closure (A : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hxCl => exact hxCl
    | inr hxInt =>
        have : (x : X) ∈ (A : Set X) := interior_subset hxInt
        exact subset_closure this
  · intro x hx
    exact Or.inl hx



theorem closure_union_three {X : Type*} [TopologicalSpace X]
    (A B C : Set X) :
    closure ((A ∪ B ∪ C) : Set X) =
      closure (A : Set X) ∪ closure B ∪ closure C := by
  calc
    closure ((A ∪ B ∪ C) : Set X)
        = closure (((A ∪ B) ∪ C) : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B : Set X) ∪ closure C := by
          simpa using
            (closure_union_eq_union_closure
              (A := (A ∪ B)) (B := C))
    _ = (closure A ∪ closure B) ∪ closure C := by
          simpa
            [closure_union_eq_union_closure (A := A) (B := B)]
    _ = closure (A : Set X) ∪ closure B ∪ closure C := by
          simpa [Set.union_assoc]

theorem interior_closure_eq_univ_of_dense_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (Set.univ : Set X) →
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
  intro hDenseInt
  -- First, rewrite `interior (closure (interior A))` using the density assumption.
  have hIntUniv :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    have :
        interior (closure (interior (A : Set X))) =
          interior ((Set.univ : Set X)) := by
      simpa [hDenseInt]
    simpa [interior_univ] using this
  -- Monotonicity of `interior` with respect to set inclusion.
  have hSubset :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    apply interior_mono
    exact closure_interior_subset_closure (A := A)
  -- Since the left‐hand side is `univ`, the right‐hand side is also `univ`.
  have hUniv :
      (Set.univ : Set X) ⊆ interior (closure (A : Set X)) := by
    simpa [hIntUniv] using hSubset
  -- Conclude the desired equality.
  exact Set.Subset.antisymm (Set.subset_univ _) hUniv

theorem closure_nonempty_iff_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)).Nonempty ↔ (A : Set X).Nonempty := by
  classical
  constructor
  · intro hCl
    by_contra hA
    have hA_eq_empty : (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hA
    have hNonempty_empty : (closure (∅ : Set X)).Nonempty := by
      simpa [hA_eq_empty] using hCl
    simpa [closure_empty] using hNonempty_empty
  · intro hA
    rcases hA with ⟨x, hxA⟩
    exact ⟨x, subset_closure hxA⟩

theorem interior_inter_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆ interior (A : Set X) := by
  intro x hx
  have h :=
    (interior_inter_subset_interiors (A := A) (B := B)) hx
  exact h.1

theorem closure_eq_union_boundary_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (A : Set X) = (A : Set X) ∪ (closure (A : Set X) \ A) := by
  simpa [hA.interior_eq] using
    (closure_eq_interior_union_closure_diff_interior (A := A))

theorem nonempty_of_interior_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty → (A : Set X).Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxInt⟩
  exact ⟨x, interior_subset hxInt⟩



theorem closure_inter_interior_subset_inter_closures {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ interior (B : Set X)) : Set X) ⊆
      closure (A : Set X) ∩ closure (B : Set X) := by
  -- We start with the inclusion into `closure A ∩ closure (interior B)`
  have h₁ :
      closure ((A ∩ interior (B : Set X)) : Set X) ⊆
        closure (A : Set X) ∩ closure (interior (B : Set X)) :=
    closure_inter_interior_subset_closure_interiors (A := A) (B := B)
  -- Since `interior B ⊆ B`, taking closures yields
  -- `closure (interior B) ⊆ closure B`.
  have h₂ : closure (interior (B : Set X)) ⊆ closure (B : Set X) :=
    closure_mono (interior_subset (s := B))
  -- Combine the two inclusions to obtain the desired result.
  intro x hx
  have hx' : (x : X) ∈ closure (A : Set X) ∩ closure (interior (B : Set X)) := h₁ hx
  exact And.intro hx'.1 (h₂ hx'.2)

theorem eq_empty_of_P1_and_empty_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      interior (A : Set X) = (∅ : Set X) →
      A = (∅ : Set X) := by
  intro hP1 hIntEmpty
  ext x
  constructor
  · intro hxA
    have h : (x : X) ∈ closure (interior (A : Set X)) := hP1 hxA
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty] using h
    exact this
  · intro hxEmpty
    cases hxEmpty

theorem closure_interior_inter_interior_complement_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∩ interior ((Aᶜ) : Set X) = (∅ : Set X) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxClInt, hxIntCompl⟩
    -- The open set `interior (Aᶜ)` contains `x`, so it must meet `interior A`
    -- since `x` lies in the closure of `interior A`.
    have hNonempty :
        ((interior ((Aᶜ) : Set X)) ∩ interior (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hxClInt _ isOpen_interior hxIntCompl
    rcases hNonempty with ⟨y, ⟨hyIntCompl, hyIntA⟩⟩
    have hyA : (y : X) ∈ (A : Set X) := interior_subset hyIntA
    have hyAc : (y : X) ∈ ((Aᶜ) : Set X) := interior_subset hyIntCompl
    have : False := hyAc hyA
    cases this
  · exact Set.empty_subset _

theorem closure_interior_inter_subset_inter_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X) ∩ B) : Set X) ⊆
      closure (interior (A : Set X)) ∩ closure (B : Set X) := by
  intro x hx
  -- `interior A ∩ B` is contained in both `interior A` and `B`
  have hA : (interior (A : Set X) ∩ B : Set X) ⊆ interior (A : Set X) := by
    intro y hy; exact hy.1
  have hB : (interior (A : Set X) ∩ B : Set X) ⊆ (B : Set X) := by
    intro y hy; exact hy.2
  -- Hence, the closure of `interior A ∩ B` is contained in the closures of
  -- `interior A` and `B`, respectively.
  have hxA : (x : X) ∈ closure (interior (A : Set X)) :=
    (closure_mono hA) hx
  have hxB : (x : X) ∈ closure (B : Set X) :=
    (closure_mono hB) hx
  exact And.intro hxA hxB

theorem subset_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (A ⊆ closure (interior (A : Set X))) := by
  intro hP2
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  simpa [Topology.P1] using hP1

theorem P3_interior_closure_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior (closure (interior (closure (A : Set X))))))) := by
  -- The set is an interior of something, hence open.
  have hOpen :
      IsOpen (interior (closure (interior (closure (interior (closure (A : Set X))))))) := by
    simpa using isOpen_interior
  -- Any open set satisfies `P3`.
  simpa using
    (Topology.P3_of_isOpen
      (A := interior (closure (interior (closure (interior (closure (A : Set X))))))) hOpen)

theorem subset_interior_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (A ⊆ interior (closure (A : Set X))) := by
  intro hP2 x hxA
  -- From `P2`, the point `x` lies in `interior (closure (interior A))`.
  have hxIntClInt : (x : X) ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  -- Use the inclusion `interior (closure (interior A)) ⊆ interior (closure A)`.
  have hSubset :=
    interior_closure_interior_subset_interior_closure (A := A)
  exact hSubset hxIntClInt

theorem P1_P2_P3_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) →
      Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  intro hBoundary
  -- An empty boundary implies that `A` is both open and closed.
  have hClopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  -- Any open set satisfies `P1`, `P2`, and `P3`.
  have hP1 : Topology.P1 (A : Set X) := Topology.P1_of_isOpen (A := A) hClopen.1
  have hP2 : Topology.P2 (A : Set X) := Topology.P2_of_isOpen (A := A) hClopen.1
  have hP3 : Topology.P3 (A : Set X) := Topology.P3_of_isOpen (A := A) hClopen.1
  exact ⟨hP1, hP2, hP3⟩

theorem interior_closure_interior_subset_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (A : Set X))) ⊆ closure (interior (A : Set X)) := by
  simpa using
    (interior_subset (s := closure (interior (A : Set X))))

theorem interior_closure_eq_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (closure (A : Set X))) :
    interior (closure (A : Set X)) = closure (A : Set X) := by
  simpa using hOpen.interior_eq