

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  dsimp [Topology.P1, Topology.P2] at hP2 ⊢
  exact fun x hx => interior_subset (hP2 hx)

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
  have hsubset : closure (interior A) ⊆ closure A := closure_mono interior_subset
  exact (interior_mono hsubset) hx₁

theorem Topology.interior_closure_interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  intro x hx
  have hsubset : closure (interior A) ⊆ closure A := closure_mono interior_subset
  exact (interior_mono hsubset) hx

theorem Topology.interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  have hx' : x ∈ interior (closure A) :=
    (Topology.interior_closure_interior_subset_interior_closure (A := A)) hx
  exact interior_subset hx'

theorem Topology.closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → closure A = closure (interior A) := by
  intro hP1
  apply Set.Subset.antisymm
  · have h' : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using h'
  · exact closure_mono interior_subset

theorem Topology.P1_of_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = closure (interior A) → Topology.P1 (A := A) := by
  intro hEq
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hEq] using this

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := interior A) := by
  dsimp [Topology.P2]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := by
    have hsubset : interior A ⊆ closure (interior A) := subset_closure
    have hx_int : x ∈ interior (interior A) := by
      simpa [interior_interior] using hx
    exact (interior_mono hsubset) hx_int
  simpa [interior_interior] using hx'

theorem Topology.closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → closure A = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 (A := A) := (Topology.P2_implies_P1 (A := A)) hP2
  exact (Topology.closure_eq_closure_interior_of_P1 (A := A)) hP1

theorem Topology.P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  · intro hEq
    exact Topology.P1_of_closure_eq_closure_interior (A := A) hEq

theorem Topology.P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 (A := A) ↔ Topology.P3 (A := A) := by
  dsimp [Topology.P2, Topology.P3]
  have h_int : interior A = A := hA.interior_eq
  simpa [h_int] using
    (Iff.rfl :
      (A ⊆ interior (closure (interior A))) ↔
      (A ⊆ interior (closure (interior A))))

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := interior A) := by
  dsimp [Topology.P3]
  intro x hx
  have hsubset : interior A ⊆ closure (interior A) := subset_closure
  have hIsOpen : IsOpen (interior A) := isOpen_interior
  have hInc : interior A ⊆ interior (closure (interior A)) :=
    interior_maximal hsubset hIsOpen
  exact hInc hx

theorem Topology.P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (A := A) := by
  dsimp [Topology.P1]
  intro x hx
  have hcl : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using hcl

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this

theorem Topology.P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hx
  have hsubset : A ⊆ closure A := subset_closure
  have hInc : A ⊆ interior (closure A) := interior_maximal hsubset hA
  exact hInc hx

theorem Topology.P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 (A := A) := by
  have hP3 : Topology.P3 (A := A) := Topology.P3_of_isOpen (A := A) hA
  have hIff := Topology.P2_iff_P3_of_open (A := A) hA
  exact hIff.mpr hP3

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 (A := A) ↔ IsOpen A := by
  constructor
  · intro hP3
    have hsubset1 : interior A ⊆ A := interior_subset
    have hsubset2 : A ⊆ interior A := by
      have h : A ⊆ interior (closure A) := hP3
      simpa [hA.closure_eq] using h
    have hEq : interior A = A := Set.Subset.antisymm hsubset1 hsubset2
    have hIsOpen : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using hIsOpen
  · intro hOpen
    exact Topology.P3_of_isOpen (A := A) hOpen

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 (A := A) ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (A := A) :=
      (Topology.P2_implies_P3 (A := A)) hP2
    exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  · intro hOpen
    exact (Topology.P2_of_isOpen (A := A)) hOpen

theorem Topology.P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.P2_of_isOpen (A := interior (closure A)) hOpen

theorem Topology.P1_iff_eq_closure_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    Topology.P1 (A := A) ↔ A = closure (interior A) := by
  simpa [hA.closure_eq] using
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A))

theorem Topology.interior_closure_eq_interior_closure_interior_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  have h : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [h]

theorem Topology.P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.P3_of_isOpen (A := interior (closure A)) hOpen

theorem Topology.P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 (A := A) → Topology.P2 (A := A) := by
  intro hP3
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  exact (Topology.P2_of_isOpen (A := A)) hOpen

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := interior (closure A)) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 (A := A) ↔ Topology.P3 (A := A) := by
  constructor
  · intro hP2
    exact (Topology.P2_implies_P3 (A := A)) hP2
  · intro hP3
    exact (Topology.P3_implies_P2_of_isClosed (A := A) hA) hP3

theorem Topology.interior_closure_eq_interior_closure_interior_of_P2 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.interior_closure_eq_interior_closure_interior_of_P1 (A := A) hP1

theorem Topology.P2_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := closure A) ↔ Topology.P3 (A := closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P2_iff_P3_of_isClosed (A := closure A) hClosed)

theorem Topology.P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → (Topology.P2 (A := A) ↔ Topology.P3 (A := A)) := by
  intro hP1
  have hEq :=
    (Topology.interior_closure_eq_interior_closure_interior_of_P1 (A := A) hP1).symm
  simpa [Topology.P2, Topology.P3, hEq]

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) :
    Topology.P2 (A := A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hxA : x ∈ interior (closure (interior A)) := hA hA_mem
      have hsubset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hInt : interior A ⊆ interior (A ∪ B) := by
          have hSub : A ⊆ A ∪ B := by
            intro z hz; exact Or.inl hz
          exact interior_mono hSub
        have hClos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hInt
        exact interior_mono hClos
      exact hsubset hxA
  | inr hB_mem =>
      have hxB : x ∈ interior (closure (interior B)) := hB hB_mem
      have hsubset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hInt : interior B ⊆ interior (A ∪ B) := by
          have hSub : B ⊆ A ∪ B := by
            intro z hz; exact Or.inr hz
          exact interior_mono hSub
        have hClos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hInt
        exact interior_mono hClos
      exact hsubset hxB

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) :
    Topology.P3 (A := A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hxA : x ∈ interior (closure A) := hA hA_mem
      have hSubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hClos : closure A ⊆ closure (A ∪ B) := closure_mono (by
          intro z hz; exact Or.inl hz)
        exact interior_mono hClos
      exact hSubset hxA
  | inr hB_mem =>
      have hxB : x ∈ interior (closure B) := hB hB_mem
      have hSubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hClos : closure B ⊆ closure (A ∪ B) := closure_mono (by
          intro z hz; exact Or.inr hz)
        exact interior_mono hClos
      exact hSubset hxB

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) :
    Topology.P1 (A := A ∪ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hxA : x ∈ closure (interior A) := hA hA_mem
      have hSubA : (A : Set X) ⊆ A ∪ B := by
        intro z hz; exact Or.inl hz
      have hIntSub : interior A ⊆ interior (A ∪ B) := interior_mono hSubA
      have hClosSub : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hIntSub
      exact hClosSub hxA
  | inr hB_mem =>
      have hxB : x ∈ closure (interior B) := hB hB_mem
      have hSubB : (B : Set X) ⊆ A ∪ B := by
        intro z hz; exact Or.inr hz
      have hIntSub : interior B ⊆ interior (A ∪ B) := interior_mono hSubB
      have hClosSub : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hIntSub
      exact hClosSub hxB

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure A) := by
  exact interior_mono subset_closure

theorem Topology.empty_is_P1_and_P2_and_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (A := (∅ : Set X)) ∧
      Topology.P2 (A := (∅ : Set X)) ∧
      Topology.P3 (A := (∅ : Set X)) := by
  constructor
  · dsimp [Topology.P1]
    intro x hx
    cases hx
  · constructor
    · dsimp [Topology.P2]
      intro x hx
      cases hx
    · dsimp [Topology.P3]
      intro x hx
      cases hx

theorem Topology.P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (A := A) ↔ Topology.P2 (A := A) := by
  constructor
  · intro _; exact Topology.P2_of_isOpen (A := A) hA
  · intro _; exact Topology.P1_of_isOpen (A := A) hA

theorem Topology.P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (A := A) ↔ Topology.P3 (A := A) := by
  have h₁ := Topology.P1_iff_P2_of_open (A := A) hA
  have h₂ := Topology.P2_iff_P3_of_open (A := A) hA
  exact h₁.trans h₂

theorem Topology.closure_eq_closure_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X}
    (hA : closure A = closure (interior A))
    (hB : closure B = closure (interior B)) :
    closure (A ∪ B) = closure (interior (A ∪ B)) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx_union : x ∈ closure A ∪ closure B := by
      have : x ∈ closure (A ∪ B) := hx
      simpa [closure_union] using this
    cases hx_union with
    | inl hxA =>
        have hxA' : x ∈ closure (interior A) := by
          simpa [hA] using hxA
        have hsubset : interior A ⊆ interior (A ∪ B) := interior_mono (by
          intro z hz; exact Or.inl hz)
        exact (closure_mono hsubset) hxA'
    | inr hxB =>
        have hxB' : x ∈ closure (interior B) := by
          simpa [hB] using hxB
        have hsubset : interior B ⊆ interior (A ∪ B) := interior_mono (by
          intro z hz; exact Or.inr hz)
        exact (closure_mono hsubset) hxB'
  · exact closure_mono (interior_subset : interior (A ∪ B) ⊆ A ∪ B)

theorem Topology.interior_closure_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure A := by
  intro x hx
  exact (interior_subset : interior (closure A) ⊆ closure A) hx

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  intro x hx
  have hsubset : closure A ⊆ closure B := closure_mono h
  exact (interior_mono hsubset) hx

theorem Topology.P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → Topology.P3 (A := A) → Topology.P2 (A := A) := by
  intro hP1 hP3
  dsimp [Topology.P2]
  intro x hxA
  have hxIntClosA : x ∈ interior (closure A) := hP3 hxA
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [hEq] using hxIntClosA

theorem Topology.interior_closure_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem Topology.P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) ↔ (Topology.P1 (A := A) ∧ Topology.P3 (A := A)) := by
  constructor
  · intro hP2
    exact And.intro
      (Topology.P2_implies_P1 (A := A) hP2)
      (Topology.P2_implies_P3 (A := A) hP2)
  · rintro ⟨hP1, hP3⟩
    exact (Topology.P1_and_P3_implies_P2 (A := A)) hP1 hP3

theorem Topology.univ_is_P1_and_P2_and_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (A := (Set.univ : Set X)) ∧
      Topology.P2 (A := (Set.univ : Set X)) ∧
      Topology.P3 (A := (Set.univ : Set X)) := by
  constructor
  · dsimp [Topology.P1]
    intro x _
    simp [interior_univ, closure_univ]
  · constructor
    · dsimp [Topology.P2]
      intro x _
      simp [interior_univ, closure_univ]
    · dsimp [Topology.P3]
      intro x _
      simp [interior_univ, closure_univ]

theorem Topology.interior_closure_interior_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :=
      Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa [closure_closure] using h
  ·
    have hSub :
        interior (closure A) ⊆ interior (closure (interior (closure A))) := by
      have h1 : (interior (closure A) : Set X) ⊆ closure (interior (closure A)) :=
        subset_closure
      have h2 : IsOpen (interior (closure A)) := isOpen_interior
      exact interior_maximal h1 h2
    intro x hx
    exact hSub hx

theorem Topology.P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 (A := A) → Topology.P1 (A := A) := by
  intro hP3
  have hP2 : Topology.P2 (A := A) :=
    (Topology.P3_implies_P2_of_isClosed (A := A) hA) hP3
  exact Topology.P2_implies_P1 (A := A) hP2

theorem Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := interior A))

theorem Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  have h1 :
      interior (closure (interior (closure A))) = interior (closure A) :=
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)
  have h2 :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) :=
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := interior (closure A))
  simpa [h1] using h2

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  intro x hx
  have hInt : interior A ⊆ interior B := interior_mono h
  have hClos : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  exact interior_mono hClos hx

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  have hInt : interior A ⊆ interior B := interior_mono h
  exact closure_mono hInt

theorem Topology.interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  have hSub : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal (subset_closure : interior A ⊆ closure (interior A))
      isOpen_interior
  exact hSub hx

theorem Topology.interior_closure_interior_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (interior A))) = interior (closure (interior A)) := by
  simpa [interior_interior]

theorem Topology.P1_iff_P2_and_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (A := A) ↔ (Topology.P2 (A := A) ∧ Topology.P3 (A := A)) := by
  constructor
  · intro hP1
    have hP2 : Topology.P2 (A := A) :=
      (Topology.P1_iff_P2_of_open (A := A) hA).1 hP1
    have hP3 : Topology.P3 (A := A) :=
      (Topology.P1_iff_P3_of_open (A := A) hA).1 hP1
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    exact Topology.P2_implies_P1 (A := A) hP2

theorem Topology.closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  simpa using (closure_mono (interior_subset : interior A ⊆ A))

theorem Topology.closure_eq_closure_interior_union_of_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 (A := A) → Topology.P1 (A := B) →
      closure (A ∪ B) = closure (interior (A ∪ B)) := by
  intro hA hB
  have hA_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hA
  have hB_eq : closure B = closure (interior B) :=
    Topology.closure_eq_closure_interior_of_P1 (A := B) hB
  exact
    Topology.closure_eq_closure_interior_union
      (A := A) (B := B) hA_eq hB_eq

theorem Topology.closure_interior_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : (A : Set X) ⊆ closure A := subset_closure
  simpa using
    (Topology.closure_interior_mono (X := X) (A := A) (B := closure A) h)

theorem Topology.interior_closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have hA : x ∈ interior (closure (interior A)) := by
    have hSubA :
        interior (closure (interior (A ∩ B))) ⊆
          interior (closure (interior A)) := by
      have hInterA : (A ∩ B : Set X) ⊆ A := by
        intro z hz
        exact hz.1
      exact
        Topology.interior_closure_interior_mono
          (X := X) (A := A ∩ B) (B := A) hInterA
    exact hSubA hx
  have hB : x ∈ interior (closure (interior B)) := by
    have hSubB :
        interior (closure (interior (A ∩ B))) ⊆
          interior (closure (interior B)) := by
      have hInterB : (A ∩ B : Set X) ⊆ B := by
        intro z hz
        exact hz.2
      exact
        Topology.interior_closure_interior_mono
          (X := X) (A := A ∩ B) (B := B) hInterB
    exact hSubB hx
  exact And.intro hA hB

theorem Topology.interior_closure_eq_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA.closure_eq]

theorem Topology.interior_union_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      have hInt : interior A ⊆ interior (A ∪ B) := interior_mono hSub
      exact hInt hA
  | inr hB =>
      have hSub : (B : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inr hy
      have hInt : interior B ⊆ interior (A ∪ B) := interior_mono hSub
      exact hInt hB

theorem Topology.isOpen_is_P1_and_P2_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 (A := A) ∧ Topology.P2 (A := A) ∧ Topology.P3 (A := A) := by
  have hP1 : Topology.P1 (A := A) := Topology.P1_of_isOpen (A := A) hA
  have hP2 : Topology.P2 (A := A) := Topology.P2_of_isOpen (A := A) hA
  have hP3 : Topology.P3 (A := A) := Topology.P3_of_isOpen (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := closure A) := by
  intro hP2
  dsimp [Topology.P1]
  intro x hx
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  have hSub : closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  have hx' : x ∈ closure (interior A) := by
    simpa [hEq] using hx
  exact hSub hx'

theorem Topology.interior_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : x ∈ interior (closure A) := by
    have hsubsetA : (A ∩ B : Set X) ⊆ A := by
      intro z hz; exact hz.1
    have hClosureSubA : closure (A ∩ B) ⊆ closure A := closure_mono hsubsetA
    exact (interior_mono hClosureSubA) hx
  have hB : x ∈ interior (closure B) := by
    have hsubsetB : (A ∩ B : Set X) ⊆ B := by
      intro z hz; exact hz.2
    have hClosureSubB : closure (A ∩ B) ⊆ closure B := closure_mono hsubsetB
    exact (interior_mono hClosureSubB) hx
  exact And.intro hA hB

theorem Topology.P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → Topology.P1 (A := closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx_closureA
  -- `closure A ⊆ closure (interior A)`
  have hSub1 : closure A ⊆ closure (interior A) := by
    have h := closure_mono (hP1)
    simpa [closure_closure] using h
  -- `closure (interior A) ⊆ closure (interior (closure A))`
  have hSub2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have hInt : interior A ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (A := A)
    exact closure_mono hInt
  have hx₁ : x ∈ closure (interior A) := hSub1 hx_closureA
  exact hSub2 hx₁

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ :
        (interior (closure (interior A)) : Set X) ⊆ closure (interior A) := by
      intro x hx
      exact (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hx
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) := closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₁ :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    simpa using h₂

theorem Topology.P2_iff_closure_eq_closure_interior_and_subset {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) ↔
      (closure A = closure (interior A) ∧ A ⊆ interior (closure A)) := by
  have h₁ := Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  have h₂ := Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  constructor
  · intro hP2
    rcases h₂.1 hP2 with ⟨hP1, hP3⟩
    exact ⟨h₁.1 hP1, hP3⟩
  · rintro ⟨hEq, hSub⟩
    have hP1 : Topology.P1 (A := A) := h₁.2 hEq
    have hP3 : Topology.P3 (A := A) := hSub
    exact h₂.2 ⟨hP1, hP3⟩

theorem Topology.closure_interior_closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- `P2` implies `P1`, giving an equality between the corresponding interiors
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
  have hIntEq :=
    Topology.interior_closure_eq_interior_closure_interior_of_P1 (A := A) hP1
  -- Rewrite the goal using `hIntEq`
  have hClosEq :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) := by
    simpa [hIntEq]
  -- Conclude with the previously established equality
  calc
    closure (interior (closure A))
        = closure (interior (closure (interior A))) := hClosEq
    _ = closure (interior A) :=
      Topology.closure_interior_closure_interior_eq_closure_interior (A := A)

theorem Topology.closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hSubA : interior (A ∩ B) ⊆ interior A := interior_mono (by
    intro z hz; exact hz.1)
  have hxA : x ∈ closure (interior A) := (closure_mono hSubA) hx
  have hSubB : interior (A ∩ B) ⊆ interior B := interior_mono (by
    intro z hz; exact hz.2)
  have hxB : x ∈ closure (interior B) := (closure_mono hSubB) hx
  exact And.intro hxA hxB

theorem Topology.closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  simpa using
    (closure_mono
      (interior_subset : interior (closure A) ⊆ closure A))

theorem Topology.closure_interior_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : interior A ⊆ interior (A ∪ B) := interior_mono (by
        intro z hz; exact Or.inl hz)
      have hClos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hSub
      exact hClos hA
  | inr hB =>
      have hSub : interior B ⊆ interior (A ∪ B) := interior_mono (by
        intro z hz; exact Or.inr hz)
      have hClos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hSub
      exact hClos hB

theorem Topology.closure_interior_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∩ B))) ⊆
      closure (interior (closure A)) ∩ closure (interior (closure B)) := by
  intro x hx
  -- auxiliary inclusions for the factor `A`
  have hAB_to_A : (A ∩ B : Set X) ⊆ A := by
    intro z hz; exact hz.1
  have hClosureAB_to_ClosureA : closure (A ∩ B) ⊆ closure A :=
    closure_mono hAB_to_A
  have hIntMonoA :
      interior (closure (A ∩ B)) ⊆ interior (closure A) :=
    interior_mono hClosureAB_to_ClosureA
  have hClosMonoA :
      closure (interior (closure (A ∩ B))) ⊆
        closure (interior (closure A)) :=
    closure_mono hIntMonoA
  -- auxiliary inclusions for the factor `B`
  have hAB_to_B : (A ∩ B : Set X) ⊆ B := by
    intro z hz; exact hz.2
  have hClosureAB_to_ClosureB : closure (A ∩ B) ⊆ closure B :=
    closure_mono hAB_to_B
  have hIntMonoB :
      interior (closure (A ∩ B)) ⊆ interior (closure B) :=
    interior_mono hClosureAB_to_ClosureB
  have hClosMonoB :
      closure (interior (closure (A ∩ B))) ⊆
        closure (interior (closure B)) :=
    closure_mono hIntMonoB
  exact And.intro (hClosMonoA hx) (hClosMonoB hx)

theorem Topology.closure_interior_closure_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure A))) = closure (interior (closure A)) := by
  have h : interior (closure (closure A)) = interior (closure A) :=
    Topology.interior_closure_closure_eq_interior_closure (X := X) (A := A)
  simpa [h]

theorem Topology.P2_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P2_of_isOpen (A := interior (closure (interior A))) hOpen

theorem Topology.closure_eq_of_subset_of_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hBClA : B ⊆ closure A) :
    closure A = closure B := by
  apply Set.Subset.antisymm
  · exact closure_mono hAB
  ·
    have h : closure B ⊆ closure (closure A) := closure_mono hBClA
    simpa [closure_closure] using h

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, use `interior_subset` to move from the interior to the closure.
  have hx₁ : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx
  -- Then, apply the monotonicity lemma already proved for closures of interiors.
  have hSub :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  exact hSub hx₁

theorem Topology.interior_closure_univ_eq_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem Topology.interior_eq_self_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    Topology.P3 (A := A) → interior A = A := by
  intro hP3
  -- `P3` together with the closedness of `A` implies that `A` is open
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  -- The interior of an open set is the set itself
  simpa using hOpen.interior_eq

theorem Topology.interior_closure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `x ∈ interior (closure A)`
      -- Since `closure A ⊆ closure (A ∪ B)`, the monotonicity of `interior`
      -- sends `hA` into the desired set.
      have hSub : closure A ⊆ closure (A ∪ B) := closure_mono (by
        intro z hz; exact Or.inl hz)
      exact (interior_mono hSub) hA
  | inr hB =>
      -- Symmetric argument for the case `x ∈ interior (closure B)`.
      have hSub : closure B ⊆ closure (A ∪ B) := closure_mono (by
        intro z hz; exact Or.inr hz)
      exact (interior_mono hSub) hB

theorem Topology.closure_interior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → closure (interior (closure A)) = closure A := by
  intro hP2
  have h₁ :
      closure (interior (closure A)) = closure (interior A) :=
    Topology.closure_interior_closure_eq_closure_interior_of_P2 (A := A) hP2
  have h₂ : closure (interior A) = closure A :=
    (Topology.closure_eq_closure_interior_of_P2 (A := A) hP2).symm
  calc
    closure (interior (closure A))
        = closure (interior A) := h₁
    _ = closure A := h₂

theorem Topology.interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  exact
    Topology.interior_union_subset_interior_union
      (X := X) (A := A) (B := B)

theorem Topology.closure_interior_interior_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.interior_eq_of_subset_of_subset_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hIntAB : interior A ⊆ B) (hBA : B ⊆ A) :
    interior A = interior B := by
  apply Set.Subset.antisymm
  ·
    have h : (interior A : Set X) ⊆ interior B :=
      interior_maximal hIntAB isOpen_interior
    exact h
  ·
    exact interior_mono hBA

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  have hClose : closure A ⊆ closure B := closure_mono h
  have hInter : interior (closure A) ⊆ interior (closure B) :=
    interior_mono hClose
  exact closure_mono hInter

theorem Topology.closure_interior_univ_eq_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hx
  have hxA : x ∈ A := interior_subset hx
  exact subset_closure hxA

theorem Topology.interior_eq_empty_of_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (∅ : Set X)) :
    interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hx
    simpa [h] using this
  · simpa using (Set.empty_subset _)

theorem Topology.interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hA : x ∈ interior A := by
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro z hz; exact hz.1
    exact (interior_mono hSub) hx
  have hB : x ∈ interior B := by
    have hSub : (A ∩ B : Set X) ⊆ B := by
      intro z hz; exact hz.2
    exact (interior_mono hSub) hx
  exact And.intro hA hB

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  simp [Topology.interior_closure_interior_closure_eq_interior_closure]

theorem Topology.closure_eq_univ_of_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro x _; exact Set.mem_univ x
  · intro x hx
    have hx_int : x ∈ interior (closure A) := by
      simpa [h] using hx
    exact (interior_subset : interior (closure A) ⊆ closure A) hx_int

theorem Topology.closure_interior_closure_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := A) → closure (interior (closure A)) = closure A := by
  intro hP3
  apply Set.Subset.antisymm
  · exact Topology.closure_interior_closure_subset_closure (A := A)
  ·
    have hSub : (A : Set X) ⊆ interior (closure A) := hP3
    exact closure_mono hSub

theorem Topology.interior_union_eq_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  simpa using hOpen.interior_eq

theorem Topology.closure_interior_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  have h :
      interior (closure (interior (closure A))) = interior (closure A) :=
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)
  simpa [h]

theorem Topology.interior_closure_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  intro x hx
  have hSub : (A \ B : Set X) ⊆ A := by
    intro z hz
    exact hz.1
  have hClosSub : closure (A \ B) ⊆ closure A := closure_mono hSub
  exact (interior_mono hClosSub) hx

theorem Topology.closure_interior_closure_eq_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) →
      closure (interior (closure A)) = closure (interior A) := by
  intro hP1
  have hInt :
      interior (closure A) = interior (closure (interior A)) :=
    Topology.interior_closure_eq_interior_closure_interior_of_P1
      (X := X) (A := A) hP1
  calc
    closure (interior (closure A))
        = closure (interior (closure (interior A))) := by
          simpa [hInt]
    _ = closure (interior A) :=
      Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := A)

theorem Topology.interior_closure_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simp [closure_empty]

theorem Topology.closure_interior_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simp

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := A) → Topology.P1 (A := closure A) := by
  intro hP3
  dsimp [Topology.P1, Topology.P3] at *
  intro x hx
  -- From `hP3`, we have `A ⊆ interior (closure A)`.
  have hSub : (A : Set X) ⊆ interior (closure A) := hP3
  -- Taking closures on both sides yields
  -- `closure A ⊆ closure (interior (closure A))`.
  have hClos : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hSub
  exact hClos hx

theorem Topology.closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 (A := A)) :
    closure (interior (closure A)) = closure (interior A) := by
  exact
    Topology.closure_interior_closure_eq_closure_interior_of_P1
      (X := X) (A := A) h

theorem Topology.P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (Set.univ : Set X) → Topology.P3 (A := A) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hDense, interior_univ]
  have hx_univ : x ∈ (Set.univ : Set X) := by
    exact Set.mem_univ x
  simpa [hInt] using hx_univ

theorem Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  simpa [interior_interior] using
    (Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := interior A))

theorem Topology.closure_eq_closure_interior_union_of_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (A := A) → Topology.P2 (A := B) →
      closure (A ∪ B) = closure (interior (A ∪ B)) := by
  intro hA hB
  have hA_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hA
  have hB_eq : closure B = closure (interior B) :=
    Topology.closure_eq_closure_interior_of_P2 (A := B) hB
  exact
    Topology.closure_eq_closure_interior_union
      (A := A) (B := B) hA_eq hB_eq

theorem Topology.P2_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 (A := Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  exact Topology.P2_of_isOpen (A := Aᶜ) hOpen

theorem Topology.interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `x ∈ interior (closure (interior A))`
      -- We show that this set is contained in the right-hand side via monotonicity.
      have hSubInt : interior A ⊆ interior (A ∪ B) := interior_mono (by
        intro z hz; exact Or.inl hz)
      have hSubClos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hSubInt
      have hSubInter :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hSubClos
      exact hSubInter hA
  | inr hB =>
      -- Symmetric argument for the case `x ∈ interior (closure (interior B))`.
      have hSubInt : interior B ⊆ interior (A ∪ B) := interior_mono (by
        intro z hz; exact Or.inr hz)
      have hSubClos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hSubInt
      have hSubInter :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hSubClos
      exact hSubInter hB

theorem Topology.P3_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 (A := Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  exact Topology.P3_of_isOpen (A := Aᶜ) hOpen

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- Using the previously proved equality of closures
  have hEq :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  -- Rewrite `hx` via `hEq` to obtain the required membership
  have : x ∈ closure (interior (closure (interior A))) := by
    simpa [hEq] using hx
  exact this

theorem Topology.P1_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P1 (A := Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  exact Topology.P1_of_isOpen (A := Aᶜ) hOpen

theorem Topology.closure_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem Topology.not_P2_of_empty_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hInt : interior A = (∅ : Set X)) (hNon : A.Nonempty) :
    ¬ Topology.P2 (A := A) := by
  intro hP2
  rcases hNon with ⟨x, hxA⟩
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hInt, closure_empty, interior_empty] using hx
  cases this

theorem Topology.P2_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (A := interior (closure (interior (closure A)))) := by
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact Topology.P2_of_isOpen
      (A := interior (closure (interior (closure A)))) hOpen

theorem Topology.closure_eq_closure_interior_of_subset
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A ⊆ closure (interior A)) :
    closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  · exact h
  · exact Topology.closure_interior_subset_closure (A := A)

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := closure A) → Topology.P3 (A := A) := by
  intro hP2
  dsimp [Topology.P3]
  intro x hxA
  have hx_closure : x ∈ closure A := subset_closure hxA
  have hx_int : x ∈ interior (closure (interior (closure A))) := hP2 hx_closure
  have hEq :=
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)
  simpa [hEq] using hx_int

theorem Topology.closure_eq_closure_interior_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    Topology.P3 (A := A) → closure A = closure (interior A) := by
  intro hP3
  have hP2 : Topology.P2 (A := A) :=
    (Topology.P3_implies_P2_of_isClosed (A := A) hA) hP3
  exact Topology.closure_eq_closure_interior_of_P2 (A := A) hP2

theorem Topology.interior_closure_interior_mono_to_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} (h : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure B) := by
  intro x hx
  -- First, use `interior_subset` to see that `interior A ⊆ B`.
  have hInt : (interior A : Set X) ⊆ B := by
    intro y hy
    exact h (interior_subset hy)
  -- Apply monotonicity of `interior ∘ closure`.
  have hIncl :=
    Topology.interior_closure_mono (X := X) (A := interior A) (B := B) hInt
  exact hIncl hx

theorem Topology.closure_interior_closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First reduction of the innermost four operations.
  have h₁ :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := A))
  -- Second reduction after replacing `A` by `interior A`.
  have h₂ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
        (X := X) (A := interior A))
  -- Assemble the reductions.
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A)))))))
        = closure (interior (closure (interior (closure (interior A))))) := by
          simpa [h₁]
    _ = closure (interior (closure (interior A))) := by
          simpa using h₂
    _ = closure (interior A) := by
          simpa using h₁



theorem Topology.interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ closure A = interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hxInt
    have hxClos : x ∈ closure A :=
      (Topology.interior_subset_closure (A := A)) hxInt
    exact And.intro hxInt hxClos

theorem Topology.closure_interior_inter_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx_ci
    have hx_cl : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (A := A)) hx_ci
    exact And.intro hx_ci hx_cl

theorem Topology.P1_of_subset_of_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hBClA : B ⊆ closure A)
    (hP1A : Topology.P1 (A := A)) : Topology.P1 (A := B) := by
  dsimp [Topology.P1] at hP1A ⊢
  intro x hxB
  -- `x ∈ closure A` since `B ⊆ closure A`
  have hx_closureA : x ∈ closure A := hBClA hxB
  -- `closure A = closure (interior A)` by `P1` for `A`
  have hClosEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1A
  -- Rewrite membership using this equality
  have hx_closureIntA : x ∈ closure (interior A) := by
    simpa [hClosEq] using hx_closureA
  -- Monotonicity from `interior A ⊆ interior B`
  have hIntAB : interior A ⊆ interior B := interior_mono hAB
  have hClosIntAB : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hIntAB
  -- Conclude the goal
  exact hClosIntAB hx_closureIntA

theorem Topology.closure_interior_closure_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure A)) ⊆ closure A`
    exact Topology.closure_interior_closure_subset_closure (A := A)
  · -- `closure A ⊆ closure (interior (closure A))`
    have hSub : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal (subset_closure : A ⊆ closure A) hA
    exact (closure_mono hSub)

theorem Topology.closure_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A := by
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro z hz
      exact hz.1
    exact (closure_mono hSub) hx
  have hxB : x ∈ closure B := by
    have hSub : (A ∩ B : Set X) ⊆ B := by
      intro z hz
      exact hz.2
    exact (closure_mono hSub) hx
  exact And.intro hxA hxB

theorem Topology.closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `A ∩ interior B` is contained in `A`
  have hSubA : (A ∩ interior B : Set X) ⊆ A := fun z hz => hz.1
  -- `A ∩ interior B` is also contained in `B`
  have hSubB : (A ∩ interior B : Set X) ⊆ B := by
    intro z hz
    exact interior_subset hz.2
  -- Monotonicity of `closure`
  have hxA : x ∈ closure A := (closure_mono hSubA) hx
  have hxB : x ∈ closure B := (closure_mono hSubB) hx
  exact And.intro hxA hxB

theorem Topology.closure_interior_closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ∩ interior (closure A) =
      interior (closure A) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxInt
    have hxClos : x ∈ closure (interior (closure A)) := by
      have hSub : (interior (closure A) : Set X) ⊆ closure (interior (closure A)) :=
        subset_closure
      exact hSub hxInt
    exact And.intro hxClos hxInt

theorem Topology.interior_closure_eq_univ_of_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  simpa [h, interior_univ]

theorem Topology.interior_closure_diff_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ closure A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have h_in_closure : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hx.1
    exact (hx.2 h_in_closure)
  · intro x hx
    cases hx

theorem Topology.closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior (closure A) = interior (closure A) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxInt
    have hxClos : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hxInt
    exact And.intro hxClos hxInt

theorem Topology.interior_closure_interior_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (interior (closure A)))) =
      interior (closure A) := by
  simpa [interior_interior] using
    (Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A))

theorem Topology.interior_closure_union_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hInt =>
      exact (Topology.interior_closure_subset_closure (A := A)) hInt
  | inr hClosInt =>
      exact (Topology.closure_interior_subset_closure (A := A)) hClosInt

theorem Topology.P3_of_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = A) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hx
  have hxInt : x ∈ interior A := by
    simpa [hInt] using hx
  have hsubset : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  exact hsubset hxInt

theorem Topology.interior_inter_closure_interior_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ closure (interior A) = interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hxInt
    have hxClos : x ∈ closure (interior A) :=
      (subset_closure : interior A ⊆ closure (interior A)) hxInt
    exact And.intro hxInt hxClos

theorem Topology.P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using this
  · intro hSub
    dsimp [Topology.P1]
    intro x hxA
    have hxClos : x ∈ closure A := subset_closure hxA
    exact hSub hxClos

theorem Topology.closure_subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) → closure A ⊆ closure (interior A) := by
  intro hP1
  exact (Topology.P1_iff_closure_subset_closure_interior (X := X) (A := A)).1 hP1

theorem Topology.P3_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P3_of_isOpen (A := interior (closure (interior A))) hOpen

theorem Topology.interior_closure_inter_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∩ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := hx.1
  have hClosA : closure A ⊆ closure (A ∪ B) := closure_mono (by
    intro y hy
    exact Or.inl hy)
  exact (interior_mono hClosA) hxA

theorem Topology.closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  simpa [hA.closure_eq] using h

theorem Topology.closure_interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  intro x hx
  -- `A \ B` is contained in `A`
  have hSub : (A \ B : Set X) ⊆ A := fun z hz => hz.1
  -- Hence, their interiors satisfy the same inclusion
  have hInt : interior (A \ B) ⊆ interior A := interior_mono hSub
  -- Taking closures preserves inclusion
  have hClos : closure (interior (A \ B)) ⊆ closure (interior A) :=
    closure_mono hInt
  exact hClos hx

theorem Topology.interior_closure_inter_subset_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∪ interior (closure B) := by
  intro x hx
  have h : x ∈ interior (closure A) ∩ interior (closure B) :=
    (Topology.interior_closure_inter_subset (A := A) (B := B)) hx
  exact Or.inl h.1

theorem Topology.interior_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior A) := by
  intro x hx
  exact (subset_closure : (interior A : Set X) ⊆ closure (interior A)) hx

theorem Topology.isClosed_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior A)) := by
  simpa using isClosed_closure (s := interior A)

theorem Topology.closure_closure_union_eq_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (closure A ∪ B) = closure (A ∪ B) := by
  simp [closure_union, closure_closure]

theorem Topology.isClosed_boundary {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure A \ interior A) := by
  have h₁ : IsClosed (closure A) := isClosed_closure
  have h₂ : IsClosed ((interior A)ᶜ) := (isOpen_interior : IsOpen (interior A)).isClosed_compl
  simpa [Set.diff_eq] using h₁.inter h₂

theorem Topology.interior_closure_union_eq_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]

theorem Topology.closure_interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure A)) := by
  -- First, we reuse an existing inclusion for interiors.
  have hSub :
      (interior (closure (interior A)) : Set X) ⊆
        closure (interior (closure A)) :=
    Topology.interior_closure_interior_subset_closure_interior_closure (A := A)
  -- Monotonicity of `closure` upgrades the inclusion.
  have hClos :
      closure (interior (closure (interior A))) ⊆
        closure (closure (interior (closure A))) :=
    closure_mono hSub
  -- Simplify the right‐hand closure of a closure.
  simpa [closure_closure] using hClos

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- We will use the characterization of the closure via open neighbourhoods.
  refine (mem_closure_iff).2 ?_
  intro U hU hxU
  -- Consider the open set `U ∩ interior B`, which still contains `x`.
  have hU' : IsOpen (U ∩ interior B) := hU.inter isOpen_interior
  have hxU' : x ∈ U ∩ interior B := ⟨hxU, hxB⟩
  -- Since `x ∈ closure A`, this open set intersects `A`.
  have hNon : ((U ∩ interior B) ∩ A).Nonempty :=
    (mem_closure_iff.1 hxA) _ hU' hxU'
  rcases hNon with ⟨y, ⟨⟨hyU, hyIntB⟩, hyA⟩⟩
  -- From `y ∈ interior B` we get `y ∈ B`.
  have hyB : y ∈ B := interior_subset hyIntB
  -- Hence `y ∈ U ∩ (A ∩ B)`.
  exact ⟨y, ⟨hyU, hyA, hyB⟩⟩

theorem Topology.interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  intro x hx
  -- Since `A \ B ⊆ A`, monotonicity of `interior` yields the desired inclusion.
  have hSub : (A \ B : Set X) ⊆ A := fun y hy => hy.1
  exact (interior_mono hSub) hx

theorem Topology.closure_interior_diff_interior_subset_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior A ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxClosInt, hxNotInt⟩
  have hxClosA : x ∈ closure A := by
    have hSub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (A := A)
    exact hSub hxClosInt
  exact And.intro hxClosA hxNotInt

theorem Topology.closure_interior_closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) ⊆ closure A := by
  -- First, rewrite the left-hand side using a previously proven equality.
  have hEq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) :=
    Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
      (X := X) (A := A)
  -- We already know `closure (interior (closure A)) ⊆ closure A`.
  have hSub :
      closure (interior (closure A)) ⊆ closure A :=
    Topology.closure_interior_closure_subset_closure (A := A)
  -- Assemble the inclusions.
  intro x hx
  have : x ∈ closure (interior (closure (interior (closure A)))) := hx
  have hx' : x ∈ closure (interior (closure A)) := by
    simpa [hEq] using this
  exact hSub hx'

theorem Topology.closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  intro x hx
  have hMono : closure (A \ B) ⊆ closure A := closure_mono (by
    intro z hz
    exact hz.1)
  exact hMono hx

theorem Topology.closure_subset_closure_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ interior (closure B)) :
    closure A ⊆ closure B := by
  -- First, take closures on both sides of the inclusion `h`.
  have h₁ : closure A ⊆ closure (interior (closure B)) := closure_mono h
  -- Then, use the previously proved inclusion
  -- `closure (interior (closure B)) ⊆ closure B`.
  have h₂ : closure (interior (closure B)) ⊆ closure B :=
    Topology.closure_interior_closure_subset_closure (A := B)
  -- Assemble the two inclusions.
  exact Set.Subset.trans h₁ h₂



theorem Topology.interior_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior (closure A))) := by
  intro x hx
  -- First inclusion: `interior A ⊆ interior (closure A)`
  have h₁ : (interior A : Set X) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  have hx₁ : x ∈ interior (closure A) := h₁ hx
  -- Second inclusion:
  -- `interior (closure A) ⊆ interior (closure (interior (closure A)))`
  have h₂ :
      (interior (closure A) : Set X) ⊆
        interior (closure (interior (closure A))) := by
    -- This follows from the same lemma applied to `interior (closure A)`
    have h :=
      Topology.interior_subset_interior_closure
        (A := interior (closure A))
    simpa [interior_interior] using h
  exact h₂ hx₁

theorem Topology.interior_closure_interior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    -- Since `interior A ⊆ A` and `A` is closed, we have
    -- `closure (interior A) ⊆ A`.
    have hSub : closure (interior A) ⊆ A := by
      have hInt : (interior A : Set X) ⊆ A := interior_subset
      have hClos : closure (interior A) ⊆ closure A := closure_mono hInt
      simpa [hA.closure_eq] using hClos
    -- Monotonicity of `interior` gives the desired inclusion.
    exact (interior_mono hSub) hx
  · intro x hx
    -- Use the maximality of the interior: if `interior A` is contained in a set,
    -- then its interior contains `interior A`.
    have hSub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have hInc : interior A ⊆ interior (closure (interior A)) :=
      interior_maximal hSub isOpen_interior
    exact hInc hx

theorem Topology.P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure A) → Topology.P3 (A := A) := by
  intro hOpen
  dsimp [Topology.P3]
  intro x hxA
  have hxClos : x ∈ closure A := subset_closure hxA
  simpa [hOpen.interior_eq] using hxClos

theorem Topology.nonempty_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A := A)) (hNon : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hNon with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩

theorem Topology.nonempty_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → A.Nonempty → (interior A).Nonempty := by
  intro hP2 hA_non
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  ·
    -- In this branch we have `interior A = ∅`.
    have hIntEq : interior A = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hInt
    -- Choose a point `x ∈ A` using the non‐emptiness of `A`.
    rcases hA_non with ⟨x, hxA⟩
    -- `P2` tells us that `x` lies in `interior (closure (interior A))`.
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    -- But this set is empty, contradicting the membership of `x`.
    have : x ∈ (∅ : Set X) := by
      simpa [hIntEq, closure_empty, interior_empty] using hxInt
    cases this

theorem Topology.closure_inter_closure_eq_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∩ closure B) = closure A ∩ closure B := by
  have hClosed : IsClosed (closure A ∩ closure B) :=
    (isClosed_closure (s := A)).inter (isClosed_closure (s := B))
  simpa using hClosed.closure_eq

theorem Topology.interior_inter_eq_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  simpa using (hA.inter hB).interior_eq

theorem Topology.interior_subset_interior_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  -- First, note that `A ⊆ closure (A ∪ B)`.
  have hSub : (A : Set X) ⊆ closure (A ∪ B) := by
    intro y hy
    -- `y ∈ A` implies `y ∈ A ∪ B`.
    have : (y : X) ∈ (A ∪ B : Set X) := Or.inl hy
    -- The universal property of the closure yields the claim.
    exact subset_closure this
  -- Monotonicity of `interior ∘ closure` gives the desired inclusion.
  exact (interior_mono hSub) hx

theorem Topology.interior_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  -- First, move `x` into `interior (A ∪ B)` using an existing lemma.
  have hxUnion : x ∈ interior (A ∪ B) :=
    (Topology.interior_union (X := X) (A := A) (B := B)) hx
  -- Since `A ∪ B ⊆ closure (A ∪ B)`, monotonicity of `interior` upgrades the membership.
  have hSub : (A ∪ B : Set X) ⊆ closure (A ∪ B) := subset_closure
  exact (interior_mono hSub) hxUnion

theorem Topology.P1_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := interior (closure (interior A))) := by
  exact Topology.P1_of_isOpen
    (A := interior (closure (interior A))) isOpen_interior

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := closure A) → Topology.P3 (A := A) := by
  intro hP3_cl
  dsimp [Topology.P3] at *
  intro x hxA
  -- First, move `x` into `closure A`.
  have hx_closure : (x : X) ∈ closure A := subset_closure hxA
  -- Apply the assumption `P3` for `closure A`.
  have hx_int_closure_closure : x ∈ interior (closure (closure A)) :=
    hP3_cl hx_closure
  -- Simplify the double closure inside the interior.
  have hIntEq :
      interior (closure (closure A)) = interior (closure A) :=
    Topology.interior_closure_closure_eq_interior_closure
      (X := X) (A := A)
  simpa [hIntEq] using hx_int_closure_closure

theorem Topology.interior_inter_interiors_eq_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (interior A ∩ interior B) = interior A ∩ interior B := by
  have hA : IsOpen (interior A) := isOpen_interior
  have hB : IsOpen (interior B) := isOpen_interior
  simpa using
    (Topology.interior_inter_eq_of_isOpen (A := interior A) (B := interior B) hA hB)

theorem Topology.P1_iff_frontier_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) ↔ frontier A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `P1` we have `closure A ⊆ closure (interior A)`.
    have hSub : closure A ⊆ closure (interior A) :=
      (Topology.closure_subset_closure_interior_of_P1 (A := A)) hP1
    -- Any point of the frontier lies in `closure A`, hence in `closure (interior A)`.
    intro x hxFrontier
    exact hSub hxFrontier.1
  · intro hFrontier
    dsimp [Topology.P1]
    intro x hxA
    by_cases hxInt : x ∈ interior A
    · -- Case `x ∈ interior A`: the claim is immediate.
      exact subset_closure hxInt
    · -- Case `x ∉ interior A`: then `x` belongs to the frontier of `A`.
      have hxFrontier : x ∈ frontier A := by
        have hxClos : x ∈ closure A := subset_closure hxA
        exact And.intro hxClos hxInt
      exact hFrontier hxFrontier

theorem Topology.P2_iff_subset_and_closure_subset {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (A := A) ↔
      (A ⊆ interior (closure A) ∧ closure A ⊆ closure (interior A)) := by
  constructor
  · intro hP2
    -- The inclusion `A ⊆ interior (closure A)` follows from `P2 → P3`.
    have hP3 : Topology.P3 (A := A) := Topology.P2_implies_P3 (A := A) hP2
    -- From `P2 → P1` we obtain the equality of the two closures.
    have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
    have hEq : closure A = closure (interior A) :=
      Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
    -- Rewrite `subset_rfl` using this equality to get the desired inclusion.
    have hClosIncl : closure A ⊆ closure (interior A) := by
      simpa [hEq] using (subset_rfl : closure A ⊆ closure A)
    exact And.intro hP3 hClosIncl
  · rintro ⟨hSubA, hClosIncl⟩
    -- To establish `P2`, start from `A ⊆ interior (closure A)`.
    dsimp [Topology.P2]
    intro x hxA
    have hxInt : x ∈ interior (closure A) := hSubA hxA
    -- Use monotonicity of `interior` with the inclusion of the closures.
    have hIntMono :
        interior (closure A) ⊆ interior (closure (interior A)) :=
      interior_mono hClosIncl
    exact hIntMono hxInt

theorem Topology.interior_inter_subset_and_isOpen_of_open {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) :
    ((interior A ∩ B : Set X) ⊆ A ∩ B) ∧ IsOpen (interior A ∩ B) := by
  constructor
  · intro x hx
    exact And.intro (interior_subset hx.1) hx.2
  · exact isOpen_interior.inter hB

theorem Topology.closure_diff_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A \ interior A) ⊆ closure A := by
  -- The set difference `A \ interior A` is clearly contained in `A`.
  have hSub : (A \ interior A : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem Topology.closure_inter_eq_inter_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  simpa using (hA.inter hB).closure_eq

theorem Topology.closure_union_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∪ interior (closure A) = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hClos => exact hClos
    | inr hInt =>
        exact (interior_subset : interior (closure A) ⊆ closure A) hInt
  · intro x hx
    exact Or.inl hx

set_option maxRecDepth 10000

theorem Topology.closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure A) = closure A := by
  simpa [closure_closure]

theorem Topology.closure_diff_interior_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A \ interior A) ∩ interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxClos, hxInt⟩
    -- Using the characterization of the closure with an open neighbourhood.
    have hNon :
        ((interior A) ∩ (A \ interior A)).Nonempty :=
      (mem_closure_iff).1 hxClos (interior A) isOpen_interior hxInt
    rcases hNon with ⟨y, ⟨hyInt, hyDiff⟩⟩
    -- `hyDiff` yields `y ∉ interior A`, contradicting `hyInt`.
    exact False.elim (hyDiff.2 hyInt)
  · exact Set.empty_subset _

theorem Topology.interior_inter_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ frontier A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxInt, hxFront⟩
    -- `hxFront` consists of membership in the closure and non-membership in the interior.
    exact (hxFront.2 hxInt).elim
  · exact Set.empty_subset _

theorem Topology.interior_closure_inter_subset_inter_interior_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    -- `closure A ∩ closure B` is included in `closure A`
    have hSub : (closure A ∩ closure B : Set X) ⊆ closure A := by
      intro y hy; exact hy.1
    exact (interior_mono hSub) hx
  have hxB : x ∈ interior (closure B) := by
    -- `closure A ∩ closure B` is included in `closure B`
    have hSub : (closure A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact (interior_mono hSub) hx
  exact And.intro hxA hxB

theorem Topology.interior_inter_eq_inter_left_of_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  apply Set.Subset.antisymm
  · intro x hx
    -- `x` lies in both `interior A` and `B`
    have hxInt : x ∈ interior A ∩ interior B :=
      (Topology.interior_inter_subset (A := A) (B := B)) hx
    have hxAB : x ∈ (A ∩ B : Set X) :=
      (interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx
    exact And.intro hxInt.1 hxAB.2
  · intro x hx
    -- `interior A ∩ B` is open and contained in `A ∩ B`
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    have hOpen : IsOpen (interior A ∩ B) :=
      isOpen_interior.inter hB
    -- Maximal property of the interior
    exact
      (interior_maximal hSub hOpen) hx

theorem Topology.interior_union_frontier_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∪ frontier A = closure A := by
  ext x
  constructor
  · intro h
    cases h with
    | inl hInt =>
        exact (Topology.interior_subset_closure (A := A)) hInt
    | inr hFront =>
        exact hFront.1
  · intro hClos
    by_cases hInt : x ∈ interior A
    · exact Or.inl hInt
    ·
      have hFront : x ∈ frontier A := And.intro hClos hInt
      exact Or.inr hFront

theorem Topology.frontier_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- Decompose the membership in the frontier of `A ∪ B`.
  have h_clos : x ∈ closure (A ∪ B) := hx.1
  have h_not_int : x ∉ interior (A ∪ B) := hx.2
  -- Rewrite the closure of a union as a union of closures.
  have h_clos_union : x ∈ closure A ∪ closure B := by
    simpa [closure_union] using h_clos
  -- If `x` were in `interior A`, it would be in `interior (A ∪ B)`,
  -- contradicting `h_not_int`.
  have h_not_intA : x ∉ interior A := by
    intro hIntA
    have : (x : X) ∈ interior (A ∪ B) := by
      have hSub : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact (interior_mono hSub) hIntA
    exact h_not_int this
  -- Analogous reasoning for `interior B`.
  have h_not_intB : x ∉ interior B := by
    intro hIntB
    have : (x : X) ∈ interior (A ∪ B) := by
      have hSub : (B : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inr hy
      exact (interior_mono hSub) hIntB
    exact h_not_int this
  -- Conclude by distinguishing the two cases for the closure.
  cases h_clos_union with
  | inl h_closA =>
      left
      exact And.intro h_closA h_not_intA
  | inr h_closB =>
      right
      exact And.intro h_closB h_not_intB

theorem Topology.closure_inter_frontier_eq_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ frontier A = frontier A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxFr
    exact And.intro hxFr.1 hxFr

theorem Topology.frontier_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior A) ⊆ closure A := by
  intro x hx
  rcases hx with ⟨hx_clos, _⟩
  have hsubset : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  exact hsubset hx_clos

theorem Topology.closure_interior_union_eq_closure_interior_union_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (A := A) → Topology.P1 (A := B) →
      closure (interior (A ∪ B)) = closure (interior A) ∪ closure (interior B) := by
  intro hP1A hP1B
  -- Equalities coming from `P1` for `A` and `B`.
  have hA_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1A
  have hB_eq : closure B = closure (interior B) :=
    Topology.closure_eq_closure_interior_of_P1 (A := B) hP1B
  -- Equality for the union obtained from `P1` on both sets.
  have hUnion_eq :
      closure (A ∪ B) = closure (interior (A ∪ B)) :=
    Topology.closure_eq_closure_interior_union_of_P1
      (A := A) (B := B) hP1A hP1B
  -- Prove both inclusions to establish set equality.
  apply Set.Subset.antisymm
  · intro x hx
    -- Convert membership using `hUnion_eq`.
    have hx_closure_union : x ∈ closure (A ∪ B) := by
      simpa [hUnion_eq] using hx
    -- Rewrite `closure (A ∪ B)` via `closure_union`.
    have hx_union : x ∈ closure A ∪ closure B := by
      simpa [closure_union] using hx_closure_union
    -- Use `hA_eq` and `hB_eq` to land in the desired union.
    cases hx_union with
    | inl hA_mem =>
        have : x ∈ closure (interior A) := by
          simpa [hA_eq] using hA_mem
        exact Or.inl this
    | inr hB_mem =>
        have : x ∈ closure (interior B) := by
          simpa [hB_eq] using hB_mem
        exact Or.inr this
  · -- The reverse inclusion is an existing lemma.
    exact
      Topology.closure_interior_union_subset_closure_interior_union
        (A := A) (B := B)

theorem Topology.closure_inter_mono_left {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (A ∩ C) ⊆ closure (B ∩ C) := by
  have hSub : (A ∩ C : Set X) ⊆ B ∩ C := by
    intro x hx
    exact And.intro (hAB hx.1) hx.2
  exact closure_mono hSub

theorem Topology.nonempty_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → A.Nonempty → (interior A).Nonempty := by
  intro hP1 hANon
  by_contra hInt
  have hIntEq : interior A = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  rcases hANon with ⟨x, hxA⟩
  have hx : x ∈ closure (interior A) := hP1 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEq, closure_empty] using hx
  cases this

theorem Topology.frontier_eq_frontier_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) → frontier A = frontier (interior A) := by
  intro hP1
  have hClos : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hClosA, hNotIntA⟩
    have hClosInt : x ∈ closure (interior A) := by
      simpa [hClos] using hClosA
    have hNotIntInt : x ∉ interior (interior A) := by
      simpa [interior_interior] using hNotIntA
    exact And.intro hClosInt hNotIntInt
  · intro hx
    rcases hx with ⟨hClosInt, hNotIntInt⟩
    have hClosA : x ∈ closure A := by
      simpa [hClos] using hClosInt
    have hNotIntA : x ∉ interior A := by
      simpa [interior_interior] using hNotIntInt
    exact And.intro hClosA hNotIntA

theorem Topology.frontier_closure_subset_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure A) ⊆ frontier A := by
  intro x hx
  -- Expand the membership condition in the frontier of `closure A`.
  rcases hx with ⟨hxClosClosA, hxNotIntClosA⟩
  -- Since `closure (closure A) = closure A`, we already have `x ∈ closure A`.
  have hxClosA : x ∈ closure A := by
    simpa [closure_closure] using hxClosClosA
  -- Show that `x ∉ interior A` using the fact that
  -- `interior A ⊆ interior (closure A)`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : (x : X) ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hxIntA
    exact hxNotIntClosA this
  -- Conclude that `x ∈ frontier A`.
  exact And.intro hxClosA hxNotIntA

theorem Topology.interior_diff_interior_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A \ interior A) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    -- `x` lies in `A \ interior A`
    have hxDiff : x ∈ A \ interior A := interior_subset hx
    -- Any open subset of `A` is contained in `interior A`
    have hSubInt :
        (interior (A \ interior A) : Set X) ⊆ interior A := by
      -- First, `interior (A \ interior A)` is contained in `A`
      have hSubA :
          (interior (A \ interior A) : Set X) ⊆ A := fun y hy =>
        (interior_subset hy).1
      -- Use the maximality of the interior
      exact interior_maximal hSubA isOpen_interior
    -- Therefore `x ∈ interior A`
    have hxInt : x ∈ interior A := hSubInt hx
    -- Contradiction with `x ∉ interior A`
    exact (hxDiff.2 hxInt).elim
  · exact Set.empty_subset _

theorem Topology.frontier_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  rcases hx with ⟨hxClosInter, hxNotIntInter⟩
  -- `x` belongs to both closures
  have hxClosA : x ∈ closure A := by
    have hSub : (A ∩ B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hxClosInter
  have hxClosB : x ∈ closure B := by
    have hSub : (A ∩ B : Set X) ⊆ B := fun y hy => hy.2
    exact (closure_mono hSub) hxClosInter
  open Classical in
  by_cases hIntA : x ∈ interior A
  · -- `x ∈ interior A`
    by_cases hIntB : x ∈ interior B
    · -- `x ∈ interior B` as well: contradiction with `hxNotIntInter`
      have hIntInter : x ∈ interior (A ∩ B) := by
        -- `interior A ∩ interior B` is an open set contained in `A ∩ B`
        have hSub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
          intro y hy; exact ⟨interior_subset hy.1, interior_subset hy.2⟩
        have hOpen : IsOpen (interior A ∩ interior B) :=
          isOpen_interior.inter isOpen_interior
        have hInc := interior_maximal hSub hOpen
        exact hInc ⟨hIntA, hIntB⟩
      exact False.elim (hxNotIntInter hIntInter)
    · -- `x ∉ interior B` ⇒ `x ∈ frontier B`
      exact Or.inr ⟨hxClosB, hIntB⟩
  · -- `x ∉ interior A` ⇒ `x ∈ frontier A`
    exact Or.inl ⟨hxClosA, hIntA⟩

theorem Topology.closure_diff_frontier_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ frontier A = interior A := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClos, hxNotFront⟩
    -- If `x ∈ closure A` but not in the frontier, then it must lie in the interior.
    by_contra hNotInt
    have hFront : x ∈ frontier A := And.intro hxClos hNotInt
    exact hxNotFront hFront
  · intro hxInt
    have hxClos : x ∈ closure A :=
      (Topology.interior_subset_closure (A := A)) hxInt
    have hxNotFront : x ∉ frontier A := by
      intro hFront
      exact hFront.2 hxInt
    exact And.intro hxClos hxNotFront

theorem Topology.closure_interior_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClosInt, hxNotInt⟩
  have hxClos : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hxClosInt
  exact And.intro hxClos hxNotInt

theorem Topology.closure_diff_interior_eq_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ interior A = frontier A := by
  rfl

theorem Topology.closure_frontier_eq_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) = frontier A := by
  have hClosed : IsClosed (frontier A) := by
    simpa using (Topology.isClosed_boundary (X := X) (A := A))
  simpa using hClosed.closure_eq

theorem Topology.closure_diff_closure_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ closure (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClosA, hxNotClosInt⟩
  have hxNotInt : x ∉ interior A := by
    intro hxInt
    have : (x : X) ∈ closure (interior A) := subset_closure hxInt
    exact hxNotClosInt this
  exact And.intro hxClosA hxNotInt

theorem Topology.frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure A := by
  intro x hx
  exact hx.1

theorem Topology.frontier_subset_closure_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure (Aᶜ) := by
  intro x hx
  rcases hx with ⟨_, hxNotInt⟩
  -- We prove that `x ∈ closure (Aᶜ)` using the neighbourhood characterization
  have : x ∈ closure (Aᶜ) := by
    refine (mem_closure_iff).2 ?_
    intro U hU hxU
    by_cases hNon : ((U ∩ (Aᶜ)) : Set X).Nonempty
    · exact hNon
    · -- If the intersection is empty, then `U ⊆ A`
      have hSub : (U : Set X) ⊆ A := by
        intro y hy
        by_contra hAy
        have : (y : X) ∈ (U ∩ Aᶜ) := ⟨hy, hAy⟩
        exact hNon ⟨y, this⟩
      -- Hence `x ∈ interior A`, contradicting `hxNotInt`
      have hxInt : x ∈ interior A :=
        (interior_maximal hSub hU) hxU
      exact (hxNotInt hxInt).elim
  exact this

theorem Topology.closure_interior_inter_frontier_eq_closure_interior_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ frontier A =
      closure (interior A) \ interior A := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClosInt, hxFront⟩
    exact And.intro hxClosInt hxFront.2
  · intro hx
    rcases hx with ⟨hxClosInt, hxNotInt⟩
    have hxClosA : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (A := A)) hxClosInt
    exact And.intro hxClosInt ⟨hxClosA, hxNotInt⟩

theorem Topology.frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClosInt, hxNotIntInt⟩
  have hxClosA : x ∈ closure A := by
    have hSub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (A := A)
    exact hSub hxClosInt
  have hxNotIntA : x ∉ interior A := by
    simpa [interior_interior] using hxNotIntInt
  exact And.intro hxClosA hxNotIntA

theorem Topology.frontier_eq_closure_interior_diff_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) →
      frontier A = closure (interior A) \ interior A := by
  intro hP1
  have hFrontierEq :=
    Topology.frontier_eq_frontier_interior_of_P1 (A := A) hP1
  calc
    frontier A = frontier (interior A) := hFrontierEq
    _ = closure (interior A) \ interior A := by
      simp [frontier, interior_interior]

theorem Topology.frontier_eq_frontier_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → frontier A = frontier (interior A) := by
  intro hP2
  have hClos : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  simp [frontier, hClos, interior_interior]

theorem Topology.frontier_eq_self_diff_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    frontier A = A \ interior A := by
  simpa [frontier, hA.closure_eq]

theorem Topology.frontier_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → frontier A ⊆ closure (interior A) := by
  intro hP2
  -- `P2` implies `P1`
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
  -- Use the characterization of `P1` via the frontier
  exact
    (Topology.P1_iff_frontier_subset_closure_interior (A := A)).1 hP1

theorem Topology.frontier_interior_eq_closure_interior_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior A) = closure (interior A) \ interior A := by
  simpa [frontier, interior_interior]

theorem Topology.closure_interior_union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∪ frontier A = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hIntClos =>
        have hSub :
            closure (interior A) ⊆ closure A :=
          Topology.closure_interior_subset_closure (A := A)
        exact hSub hIntClos
    | inr hFront =>
        exact hFront.1
  · intro hxClos
    by_cases hInt : x ∈ interior A
    · -- `x ∈ interior A`, hence in `closure (interior A)`
      have hxIntClos : x ∈ closure (interior A) := subset_closure hInt
      exact Or.inl hxIntClos
    · -- `x ∉ interior A`, so `x` lies in the frontier of `A`
      have hxFront : x ∈ frontier A := And.intro hxClos hInt
      exact Or.inr hxFront

theorem Topology.closure_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (closure (interior A)) ⊆ closure A := by
  -- First, eliminate the redundant double closure.
  have h_eq : closure (closure (interior A)) = closure (interior A) := by
    simpa [closure_closure]
  -- Then use the already known inclusion for a single closure of the interior.
  have h_sub : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  simpa [h_eq] using h_sub

theorem Topology.closure_closed_left_inter_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) :
    closure A ∩ closure B = A ∩ closure B := by
  simpa [hA.closure_eq]

theorem Topology.closure_inter_closure_compl_eq_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ closure (Aᶜ) = frontier A := by
  ext x
  constructor
  · -- `→`  direction
    intro hx
    rcases hx with ⟨hxClosA, hxClosCompl⟩
    have hxNotInt : x ∉ interior A := by
      intro hInt
      -- Since `x ∈ closure (Aᶜ)`, every open neighbourhood of `x`
      -- meets `Aᶜ`. Taking `interior A`, we obtain a contradiction.
      have hNonempty :=
        (mem_closure_iff.1 hxClosCompl) (interior A) isOpen_interior hInt
      rcases hNonempty with ⟨y, ⟨hyInt, hyCompl⟩⟩
      have hyA : y ∈ A := interior_subset hyInt
      exact hyCompl hyA
    exact And.intro hxClosA hxNotInt
  · -- `←` direction
    intro hxFront
    have hxClosA : x ∈ closure A := hxFront.1
    have hxClosCompl : x ∈ closure (Aᶜ) :=
      (Topology.frontier_subset_closure_compl (A := A)) hxFront
    exact And.intro hxClosA hxClosCompl

theorem Topology.closure_inter_closure_subset_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- First show `x ∈ closure A`.
  have hxClosA : x ∈ closure A := by
    have hSub : (A ∩ closure B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hx
  -- Then show `x ∈ closure B`.
  have hxClosB : x ∈ closure B := by
    have hSub : (A ∩ closure B : Set X) ⊆ closure B := fun y hy => hy.2
    have hx' : x ∈ closure (closure B) := (closure_mono hSub) hx
    simpa [closure_closure] using hx'
  exact And.intro hxClosA hxClosB



theorem Topology.frontier_frontier_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (frontier A) ⊆ frontier A := by
  intro x hx
  -- `frontier A` is closed, hence its closure is itself.
  have hClosed : IsClosed (frontier A) := Topology.isClosed_boundary (A := A)
  have hClosureEq : closure (frontier A) = frontier A := hClosed.closure_eq
  -- From `x ∈ frontier (frontier A)` we get `x ∈ closure (frontier A)`,
  -- which equals `frontier A`.
  have hxFront : x ∈ frontier A := by
    have : x ∈ closure (frontier A) := hx.1
    simpa [hClosureEq] using this
  exact hxFront

theorem Topology.frontier_eq_closure_diff_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    frontier A = closure A \ A := by
  simpa [frontier, hA.interior_eq]

theorem Topology.interior_inter_eq_inter_right_of_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  -- Apply the existing lemma with the factors swapped.
  have h :=
    Topology.interior_inter_eq_inter_left_of_isOpen_right
      (A := B) (B := A) hA
  simpa [Set.inter_comm] using h

theorem Topology.frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    frontier A ⊆ A := by
  intro x hx
  have hx_closure : x ∈ closure A := hx.1
  simpa [hA.closure_eq] using hx_closure

theorem Topology.interior_closure_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ interior A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxIntClos, hxNotIntA⟩
  have hxClosA : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
  exact And.intro hxClosA hxNotIntA

theorem Topology.frontier_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (Aᶜ) = frontier A := by
  calc
    frontier (Aᶜ)
        = closure (Aᶜ) ∩ closure ((Aᶜ)ᶜ) := by
          simpa using
            (Topology.closure_inter_closure_compl_eq_frontier
              (X := X) (A := Aᶜ)).symm
    _ = closure A ∩ closure (Aᶜ) := by
          simp [compl_compl, Set.inter_comm, Set.inter_left_comm]
    _ = frontier A := by
          simpa using
            (Topology.closure_inter_closure_compl_eq_frontier
              (X := X) (A := A)).symm

theorem Topology.closure_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    -- Derive a contradiction from the assumption that `x` belongs to
    -- both `closure A` and `interior (Aᶜ)`.
    rcases hx with ⟨hxClos, hxIntCompl⟩
    -- Using the characterization of the closure via neighborhood
    -- intersections with open sets.
    have hNon :
        ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClos _ isOpen_interior hxIntCompl
    rcases hNon with ⟨y, ⟨hyIntCompl, hyA⟩⟩
    -- But `interior (Aᶜ)` is contained in `Aᶜ`, contradicting `y ∈ A`.
    have : (y : X) ∈ Aᶜ :=
      (interior_subset : interior (Aᶜ) ⊆ Aᶜ) hyIntCompl
    exact (this hyA).elim
  · intro x hx
    -- The right-hand side is the empty set.
    cases hx

theorem Topology.frontier_eq_closure_interior_diff_interior_of_P2 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) →
      frontier A = closure (interior A) \ interior A := by
  intro hP2
  calc
    frontier A
        = frontier (interior A) := by
          simpa using
            (Topology.frontier_eq_frontier_interior_of_P2 (A := A) hP2)
    _ = closure (interior A) \ interior A := by
          simpa using
            (Topology.frontier_interior_eq_closure_interior_diff_interior
              (X := X) (A := A))

theorem Topology.closure_diff_subset_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClos, hxNotA⟩
  have hxNotInt : x ∉ interior A := by
    intro hxInt
    exact hxNotA (interior_subset hxInt)
  exact And.intro hxClos hxNotInt

theorem Topology.frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    frontier A ⊆ closure B := by
  intro x hx
  have hxClosA : x ∈ closure A := hx.1
  have hSub : closure A ⊆ closure B := closure_mono hAB
  exact hSub hxClosA

theorem Topology.frontier_interior_eq_closure_interior_inter_frontier {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier (interior A) = closure (interior A) ∩ frontier A := by
  have h₁ :=
    Topology.frontier_interior_eq_closure_interior_diff_interior
      (X := X) (A := A)
  have h₂ :=
    Topology.closure_interior_inter_frontier_eq_closure_interior_diff_interior
      (X := X) (A := A)
  calc
    frontier (interior A)
        = closure (interior A) \ interior A := by
          simpa using h₁
    _ = closure (interior A) ∩ frontier A := by
          simpa using (h₂.symm)

theorem Topology.closure_eq_self_union_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A = A ∪ frontier A := by
  ext x
  constructor
  · intro hxClos
    by_cases hA : x ∈ A
    · exact Or.inl hA
    ·
      have hxNotInt : x ∉ interior A := by
        intro hxInt
        exact hA (interior_subset hxInt)
      have hxFront : x ∈ frontier A := And.intro hxClos hxNotInt
      exact Or.inr hxFront
  · intro hx
    cases hx with
    | inl hA      => exact subset_closure hA
    | inr hFront  => exact hFront.1

theorem Topology.frontier_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- From `hx` we know `x ∈ closure (A ∩ B)`.
  have hxClos : x ∈ closure (A ∩ B) := hx.1
  -- Deduce `x ∈ closure A` since `A ∩ B ⊆ A`.
  have hxA : x ∈ closure A := by
    have hSub : (A ∩ B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hxClos
  -- Deduce `x ∈ closure B` since `A ∩ B ⊆ B`.
  have hxB : x ∈ closure B := by
    have hSub : (A ∩ B : Set X) ⊆ B := fun y hy => hy.2
    exact (closure_mono hSub) hxClos
  exact And.intro hxA hxB

theorem Topology.interior_subset_diff_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ A \ frontier A := by
  intro x hxInt
  have hxA : x ∈ A := interior_subset hxInt
  have hxNotFront : x ∉ frontier A := by
    intro hxFront
    have hNotInt : x ∉ interior A := hxFront.2
    exact hNotInt hxInt
  exact And.intro hxA hxNotFront

theorem Topology.frontier_closure_eq_closure_diff_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier (closure A) = closure A \ interior (closure A) := by
  simp [frontier, closure_closure]

theorem Topology.interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact (subset_closure : interior (closure A) ⊆ closure (interior (closure A))) hx

theorem Topology.interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior A) = interior A := by
  simpa [interior_interior]

theorem Topology.frontier_union_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∪ B) ⊆ closure A ∪ closure B := by
  intro x hx
  have : (x : X) ∈ closure (A ∪ B) := hx.1
  simpa [closure_union] using this

theorem Topology.interior_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ closure B) :
    interior A ⊆ closure B := by
  intro x hxInt
  have hxA : x ∈ A := interior_subset hxInt
  exact hAB hxA

theorem Topology.interior_closure_diff_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxIntClos, hxNotA⟩
  -- `x ∈ closure A` because `interior (closure A) ⊆ closure A`
  have hxClos : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
  -- `x ∉ interior A` since `interior A ⊆ A`
  have hxNotInt : x ∉ interior A := by
    intro hxIntA
    have : (x : X) ∈ A := interior_subset hxIntA
    exact hxNotA this
  exact And.intro hxClos hxNotInt

theorem Topology.frontier_eq_empty_of_isOpen_and_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hOpen : IsOpen A) (hClosed : IsClosed A) :
    frontier A = (∅ : Set X) := by
  have hClosure : closure A = A := hClosed.closure_eq
  have hInterior : interior A = A := hOpen.interior_eq
  simp [frontier, hClosure, hInterior]

theorem Topology.P3_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (Set.univ : Set X)) :
    Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x _
  have : (x : X) ∈ (Set.univ : Set X) := by
    exact Set.mem_univ x
  simpa [h] using this

theorem Topology.closure_subset_interior_closure_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ⊆ interior (closure A) ∪ frontier A := by
  intro x hxClos
  by_cases hInt : x ∈ interior (closure A)
  · exact Or.inl hInt
  ·
    have hNotIntA : x ∉ interior A := by
      intro hIntA
      have : x ∈ interior (closure A) :=
        (Topology.interior_subset_interior_closure (A := A)) hIntA
      exact hInt this
    have hxFront : x ∈ frontier A := And.intro hxClos hNotIntA
    exact Or.inr hxFront

theorem Topology.frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier A = closure A \ interior A := by
  rfl

theorem Topology.P1_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P1 (A := A) := by
  intro hDense
  dsimp [Topology.P1]
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    exact Set.mem_univ x
  simpa [hDense] using this



theorem Topology.interior_diff_subset_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B) ⊆ A \ closure B := by
  intro x hxInt
  -- `x` lies in `A \ B`.
  have hAB : x ∈ A \ B := interior_subset hxInt
  have hA : x ∈ A := hAB.1
  -- We show `x ∉ closure B`.
  have hNotClB : x ∉ closure B := by
    intro hxClB
    -- The open neighbourhood `U := interior (A \ B)` of `x`
    -- must intersect `B` because `x ∈ closure B`.
    have hNon :
        ((interior (A \ B) : Set X) ∩ B).Nonempty :=
      (mem_closure_iff).1 hxClB (interior (A \ B)) isOpen_interior hxInt
    rcases hNon with ⟨y, ⟨hyInt, hyB⟩⟩
    -- But `y ∈ interior (A \ B)` implies `y ∉ B`, contradiction.
    have hNotB : y ∉ B := (interior_subset hyInt).2
    exact hNotB hyB
  exact And.intro hA hNotClB

theorem Topology.interior_closure_subset_interior_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ interior A ∪ frontier A := by
  intro x hxIntClos
  by_cases hIntA : x ∈ interior A
  · exact Or.inl hIntA
  ·
    have hClosA : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
    have hFront : x ∈ frontier A := And.intro hClosA hIntA
    exact Or.inr hFront

theorem Topology.closure_inter_interior_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior A = interior A := by
  have h := Topology.interior_inter_closure_eq_interior (X := X) (A := A)
  simpa [Set.inter_comm] using h.symm

theorem Topology.self_diff_frontier_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    A \ frontier A = interior A := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxA, hNotFront⟩
    by_cases hInt : x ∈ interior A
    · exact hInt
    ·
      have hFront : x ∈ frontier A := And.intro (subset_closure hxA) hInt
      exact (hNotFront hFront).elim
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    have hNotFront : x ∉ frontier A := by
      intro hFront
      exact hFront.2 hxInt
    exact And.intro hxA hNotFront

theorem Topology.closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- We prove `x ∈ closure (A \ B)` via the characterization
  -- of the closure in terms of open neighbourhoods.
  have hMem : ∀ U, IsOpen U → x ∈ U → ((U ∩ (A \ B) : Set X)).Nonempty := by
    intro U hU hxU
    -- Choose an open neighbourhood of `x` disjoint from `B`.
    have hV : IsOpen ((closure B)ᶜ) :=
      (isClosed_closure (s := B)).isOpen_compl
    have hxV : x ∈ (closure B)ᶜ := by
      simpa using hxNotB
    -- Intersect the two open neighbourhoods.
    let W := U ∩ (closure B)ᶜ
    have hW_open : IsOpen W := hU.inter hV
    have hxW : x ∈ W := And.intro hxU hxV
    -- Since `x ∈ closure A`, `W ∩ A` is nonempty.
    have hNon : ((W ∩ A : Set X)).Nonempty :=
      (mem_closure_iff).1 hxA W hW_open hxW
    rcases hNon with ⟨y, ⟨⟨hyU, hyV⟩, hyA⟩⟩
    -- `y ∉ B` because `y ∈ (closure B)ᶜ`, hence `y ∈ A \ B`.
    have hyNotB : y ∉ B := by
      intro hyB
      have : (y : X) ∈ closure B := subset_closure hyB
      exact hyV this
    exact ⟨y, And.intro hyU (And.intro hyA hyNotB)⟩
  exact (mem_closure_iff).2 hMem

theorem Topology.isClosed_closure_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsClosed (closure A ∩ closure B) := by
  exact (isClosed_closure (s := A)).inter (isClosed_closure (s := B))

theorem Topology.isOpen_and_isClosed_of_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier A = (∅ : Set X) → IsOpen A ∧ IsClosed A := by
  intro hFrontier
  -- Step 1: show `closure A ⊆ interior A`
  have hClosSubInt : closure A ⊆ interior A := by
    intro x hxClos
    by_cases hInt : x ∈ interior A
    · exact hInt
    ·
      have hFront : x ∈ frontier A := And.intro hxClos hInt
      have : False := by
        simpa [hFrontier] using hFront
      exact this.elim
  -- Step 2: deduce `A ⊆ interior A`
  have hASubInt : (A : Set X) ⊆ interior A := by
    intro x hxA
    exact hClosSubInt (subset_closure hxA)
  -- Equalities `interior A = A` and `closure A = A`
  have hIntEq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · exact hASubInt
  have hClosEq : closure A = A := by
    apply Set.Subset.antisymm
    · intro x hxClos
      exact interior_subset (hClosSubInt hxClos)
    · exact subset_closure
  -- Conclude openness and closedness
  have hOpen : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [hIntEq] using this
  have hClosed : IsClosed A := by
    have : IsClosed (closure A) := isClosed_closure
    simpa [hClosEq] using this
  exact And.intro hOpen hClosed

theorem Topology.interior_closure_subset_self_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ A ∪ frontier A := by
  intro x hx
  -- First, use the existing inclusion into `interior A ∪ frontier A`.
  have h : x ∈ interior A ∪ frontier A :=
    (Topology.interior_closure_subset_interior_union_frontier (A := A)) hx
  -- Upgrade the membership from `interior A` to `A` when necessary.
  cases h with
  | inl hInt =>
      exact Or.inl (interior_subset hInt)
  | inr hFront =>
      exact Or.inr hFront

theorem Topology.frontier_eq_empty_iff_isOpen_and_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = (∅ : Set X) ↔ (IsOpen A ∧ IsClosed A) := by
  constructor
  · intro h
    exact
      Topology.isOpen_and_isClosed_of_frontier_eq_empty
        (X := X) (A := A) h
  · rintro ⟨hOpen, hClosed⟩
    exact
      Topology.frontier_eq_empty_of_isOpen_and_isClosed
        (X := X) (A := A) hOpen hClosed

theorem Topology.interior_closure_union_frontier_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure A) ∪ frontier A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hInt =>
        exact (interior_subset : interior (closure A) ⊆ closure A) hInt
    | inr hFront =>
        exact (Topology.frontier_subset_closure (A := A)) hFront
  · exact Topology.closure_subset_interior_closure_union_frontier (A := A)

theorem Topology.frontier_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (frontier A) ⊆ closure A := by
  intro x hx
  have h_front : x ∈ frontier A :=
    (Topology.frontier_frontier_subset_frontier (A := A)) hx
  exact (Topology.frontier_subset_closure (A := A)) h_front

theorem Topology.isClosed_iff_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A ↔ closure A ⊆ A := by
  constructor
  · intro hClosed
    simpa [hClosed.closure_eq]
  · intro hSubset
    have hEq : closure A = A := Set.Subset.antisymm hSubset subset_closure
    simpa [hEq] using (isClosed_closure (s := A))

theorem Topology.frontier_subset_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : frontier A ⊆ Aᶜ := by
  intro x hx
  -- `hx` gives `x ∉ interior A`.
  have hNotInt : x ∉ interior A := hx.2
  -- Since `A` is open, `interior A = A`.
  have hIntEq : interior A = A := hA.interior_eq
  -- Therefore, `x ∉ A`.
  have hNotA : x ∉ A := by
    simpa [hIntEq] using hNotInt
  -- Hence, `x ∈ Aᶜ`.
  simpa using hNotA

theorem Topology.frontier_eq_empty_of_closure_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = interior A) :
    frontier A = (∅ : Set X) := by
  simpa [frontier, h, Set.diff_self]

theorem Topology.interior_compl_inter_frontier_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ) ∩ frontier A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxIntCompl, hxFront⟩
    have hxClosA : x ∈ closure A := hxFront.1
    -- The open neighbourhood `interior (Aᶜ)` of `x` is disjoint from `A`,
    -- contradicting `x ∈ closure A`.
    have hNon :
        ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClosA (interior (Aᶜ)) isOpen_interior hxIntCompl
    rcases hNon with ⟨y, ⟨hyIntCompl, hyA⟩⟩
    have : (y : X) ∈ Aᶜ := interior_subset hyIntCompl
    exact (this hyA).elim
  · exact Set.empty_subset _

theorem Topology.frontier_subset_compl_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    (frontier A ⊆ Aᶜ) ↔ IsOpen A := by
  constructor
  · intro hSub
    -- We prove that every point of `A` is interior, hence `A` is open.
    have hInt : (A : Set X) ⊆ interior A := by
      intro x hxA
      by_cases hxInt : x ∈ interior A
      · exact hxInt
      ·
        -- If `x ∉ interior A`, then `x` lies in the frontier of `A`.
        have hxFront : x ∈ frontier A := by
          have hxClos : x ∈ closure A := subset_closure hxA
          exact And.intro hxClos hxInt
        -- But the frontier is assumed to be contained in `Aᶜ`, contradicting `x ∈ A`.
        have : x ∈ Aᶜ := hSub hxFront
        exact (this hxA).elim
    -- Since `interior A ⊆ A` always holds, we have `interior A = A`.
    have hEq : interior A = A := Set.Subset.antisymm interior_subset hInt
    simpa [hEq] using (isOpen_interior : IsOpen (interior A))
  · intro hOpen
    exact frontier_subset_compl_of_isOpen (A := A) hOpen

theorem Topology.frontier_eq_compl_of_open_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) (hDense : closure A = (Set.univ : Set X)) :
    frontier A = Aᶜ := by
  calc
    frontier A = closure A \ interior A := rfl
    _ = (Set.univ : Set X) \ A := by
      simpa [hOpen.interior_eq, hDense]
    _ = Aᶜ := by
      ext x
      simp

theorem Topology.interior_eq_self_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 (A := A) → interior A = A := by
  intro hP2
  have hP3 : Topology.P3 (A := A) := Topology.P2_implies_P3 (A := A) hP2
  exact Topology.interior_eq_self_of_isClosed_and_P3 (A := A) hA hP3

theorem Topology.closure_diff_interiorClosure_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior (closure A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClos, hxNotIntClos⟩
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hxIntA
    exact hxNotIntClos this
  exact And.intro hxClos hxNotIntA

theorem Topology.frontier_interior_eq_frontier_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    frontier (interior A) = frontier A := by
  have hInt : interior A = A := hA.interior_eq
  simpa [frontier, hInt, interior_interior]

theorem Topology.frontier_eq_compl_interior_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : closure A = (Set.univ : Set X)) :
    frontier A = (interior A)ᶜ := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxNotInt
    have hxClos : x ∈ closure A := by
      have : x ∈ (Set.univ : Set X) := Set.mem_univ x
      simpa [hDense] using this
    exact And.intro hxClos hxNotInt

theorem Topology.frontier_closure_eq_frontier_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    frontier (closure A) = frontier A := by
  simpa [frontier, hA.closure_eq, closure_closure]

theorem Topology.frontier_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  simpa [Set.diff_eq, frontier_compl] using
    (Topology.frontier_inter_subset (A := A) (B := Bᶜ))

theorem Topology.closure_frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (frontier A) = closure A \ interior A := by
  have h := Topology.closure_frontier_eq_frontier (A := A)
  simpa [h] using
    (Topology.closure_diff_interior_eq_frontier (A := A)).symm

theorem Topology.frontier_inter_subset_frontier_inter_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆
      (frontier A ∩ closure B) ∪ (frontier B ∩ closure A) := by
  intro x hx
  -- Decompose the hypothesis `hx`.
  rcases hx with ⟨hxClosInter, hxNotIntInter⟩
  -- Membership in the individual closures.
  have hxClosA : x ∈ closure A := by
    have hSub : (A ∩ B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hxClosInter
  have hxClosB : x ∈ closure B := by
    have hSub : (A ∩ B : Set X) ⊆ B := fun y hy => hy.2
    exact (closure_mono hSub) hxClosInter
  -- Case distinction on `x ∈ interior A`.
  by_cases hIntA : x ∈ interior A
  · -- If `x ∈ interior A`, then `x ∉ interior B`.
    have hNotIntB : x ∉ interior B := by
      intro hIntB
      -- `x` would then lie in `interior (A ∩ B)`, contradicting `hxNotIntInter`.
      have hSub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
        intro y hy; exact ⟨interior_subset hy.1, interior_subset hy.2⟩
      have hOpen : IsOpen (interior A ∩ interior B) :=
        isOpen_interior.inter isOpen_interior
      have hInc : (interior A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
        interior_maximal hSub hOpen
      have : x ∈ interior (A ∩ B) := hInc ⟨hIntA, hIntB⟩
      exact hxNotIntInter this
    -- Assemble membership in `frontier B ∩ closure A`.
    have hFrontB : x ∈ frontier B := And.intro hxClosB hNotIntB
    exact Or.inr ⟨hFrontB, hxClosA⟩
  · -- Otherwise `x ∉ interior A`, so `x ∈ frontier A`.
    have hFrontA : x ∈ frontier A := And.intro hxClosA hIntA
    exact Or.inl ⟨hFrontA, hxClosB⟩

theorem Topology.frontier_univ_eq_empty {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  have hClosed : IsClosed (Set.univ : Set X) := isClosed_univ
  simpa using
    (Topology.frontier_eq_empty_of_isOpen_and_isClosed
      (A := (Set.univ : Set X)) hOpen hClosed)

theorem Topology.P3_implies_P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P3 (A := A) → Topology.P1 (A := A) := by
  intro hP3
  have hEquiv := Topology.P1_iff_P3_of_open (A := A) hA
  exact (hEquiv.mpr hP3)

theorem Topology.closure_diff_subset_closure_diff_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A \ interior B := by
  intro x hx
  -- First, prove `x ∈ closure A`.
  have hxClosA : x ∈ closure A := by
    have hSub : (A \ B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hx
  -- Next, show `x ∉ interior B` by contradiction.
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- Since `x ∈ closure (A \ B)`, every neighbourhood of `x`
    -- meets `A \ B`. Take `interior B`, an open neighbourhood of `x`.
    have hNon :
        ((interior B : Set X) ∩ (A \ B)).Nonempty :=
      (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
    rcases hNon with ⟨y, ⟨hyIntB, hyDiff⟩⟩
    -- But `y ∈ interior B ⊆ B`, contradicting `y ∉ B`.
    have : (y : X) ∈ B := (interior_subset : interior B ⊆ B) hyIntB
    exact hyDiff.2 this
  -- Assemble the two facts.
  exact And.intro hxClosA hxNotIntB

theorem Topology.frontier_eq_self_of_isClosed_and_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hInt : interior A = (∅ : Set X)) :
    frontier A = A := by
  have h :=
    Topology.frontier_eq_self_diff_interior_of_isClosed
      (X := X) (A := A) hA
  simpa [hInt] using h

theorem Topology.frontier_eq_compl_interior_union_interior_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = (interior A ∪ interior (Aᶜ))ᶜ := by
  ext x
  constructor
  · intro hx
    -- `hx` gives `x ∈ closure A` and `x ∉ interior A`
    have hNotIntA : x ∉ interior A := hx.2
    -- Show that `x ∉ interior (Aᶜ)`
    have hNotIntAc : x ∉ interior (Aᶜ) := by
      intro hxIntAc
      -- `interior (Aᶜ)` is open and contains `x`
      -- but it is disjoint from `A`, contradicting `x ∈ closure A`.
      have hNon :
          ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
        (mem_closure_iff).1 hx.1 (interior (Aᶜ)) isOpen_interior hxIntAc
      rcases hNon with ⟨y, ⟨hyIntAc, hyA⟩⟩
      have : (y : X) ∈ Aᶜ := interior_subset hyIntAc
      exact this hyA
    -- Hence `x` lies in the complement of the union of the interiors.
    have : x ∉ interior A ∪ interior (Aᶜ) := by
      intro h
      cases h with
      | inl hIntA  => exact hNotIntA hIntA
      | inr hIntAc => exact hNotIntAc hIntAc
    simpa [Set.mem_compl] using this
  · intro hxComp
    -- `hxComp` says `x` is not in `interior A` nor in `interior (Aᶜ)`
    have hNotUnion : x ∉ interior A ∪ interior (Aᶜ) := by
      simpa [Set.mem_compl] using hxComp
    have hNotIntA : x ∉ interior A := by
      intro hIntA
      exact hNotUnion (Or.inl hIntA)
    have hNotIntAc : x ∉ interior (Aᶜ) := by
      intro hIntAc
      exact hNotUnion (Or.inr hIntAc)
    -- Show `x ∈ closure A`
    have hClos : x ∈ closure A := by
      by_contra hNotClos
      have hxOpen : x ∈ (closure A)ᶜ := hNotClos
      have hOpenCompl : IsOpen ((closure A)ᶜ) :=
        (isClosed_closure (s := A)).isOpen_compl
      -- `(closure A)ᶜ` is an open neighbourhood of `x` contained in `Aᶜ`
      have hSub : ((closure A)ᶜ : Set X) ⊆ Aᶜ := by
        intro y hy
        by_cases hyA : y ∈ A
        · have : y ∈ closure A := subset_closure hyA
          exact (hy this).elim
        · exact hyA
      have hxIntAc : x ∈ interior (Aᶜ) :=
        (interior_maximal hSub hOpenCompl) hxOpen
      exact hNotIntAc hxIntAc
    exact And.intro hClos hNotIntA

theorem Topology.closure_union_right_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    closure (A ∪ B) = closure A ∪ B := by
  simpa [closure_union, hB.closure_eq]

theorem Topology.closure_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro _ _
    exact Set.mem_univ _
  · intro x _
    by_cases hA : x ∈ A
    · exact Or.inl (subset_closure hA)
    · have : x ∈ Aᶜ := hA
      exact Or.inr (subset_closure this)

theorem Topology.P1_closure_iff_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := closure A) ↔
      closure A = closure (interior (closure A)) := by
  -- Apply the general `P1` characterization to the set `closure A`
  have h :=
    Topology.P1_iff_closure_eq_closure_interior (X := X) (A := closure A)
  -- Simplify the double closure appearing in `h`
  simpa [closure_closure] using h

theorem Topology.isClosed_of_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : frontier A ⊆ A) : IsClosed A := by
  -- First, we show `closure A ⊆ A`.
  have hClosSub : closure A ⊆ A := by
    intro x hxClos
    -- Using `interior A ∪ frontier A = closure A`, we know that
    -- `x ∈ interior A ∪ frontier A`.
    have hxUnion : x ∈ interior A ∪ frontier A := by
      simpa [Topology.interior_union_frontier_eq_closure (A := A)] using hxClos
    -- We distinguish the two cases.
    cases hxUnion with
    | inl hInt =>
        -- `x ∈ interior A ⊆ A`
        exact (interior_subset : interior A ⊆ A) hInt
    | inr hFront =>
        -- `x ∈ frontier A ⊆ A` by the hypothesis `h`
        exact h hFront
  -- The inclusion `closure A ⊆ A` implies that `A` is closed.
  have hClosed : IsClosed A := by
    have hEquiv := (Topology.isClosed_iff_closure_subset (A := A))
    exact hEquiv.2 hClosSub
  simpa using hClosed

theorem Topology.interior_inter_interior_closure_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ interior (closure A) = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hx' : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hx
    exact And.intro hx hx'

theorem Topology.frontier_eq_closure_compl_diff_interior_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = closure (Aᶜ) \ interior (Aᶜ) := by
  calc
    frontier A = frontier (Aᶜ) := by
      simpa using (Topology.frontier_compl (A := A)).symm
    _ = closure (Aᶜ) \ interior (Aᶜ) := by
      simpa using
        (Topology.frontier_eq_closure_diff_interior (A := Aᶜ))

theorem Topology.closure_union_closure_right_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ closure B) = closure (A ∪ B) := by
  have hClosed : IsClosed (closure B) := isClosed_closure
  have h₁ := Topology.closure_union_right_closed (A := A) (B := closure B) hClosed
  calc
    closure (A ∪ closure B) = closure A ∪ closure B := by
      simpa using h₁
    _ = closure (A ∪ B) := by
      simpa [closure_union]

theorem Topology.frontier_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    frontier (∅ : Set X) = (∅ : Set X) := by
  simp [frontier]

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure (interior A)))))))) =
      interior (closure (interior A)) := by
  simp [Topology.interior_closure_interior_closure_eq_interior_closure,
        closure_closure, interior_interior]

theorem Topology.interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure A) → interior (closure A) = closure A := by
  intro hOpen
  simpa using hOpen.interior_eq

theorem Topology.frontier_symmDiff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier ((A \ B) ∪ (B \ A)) ⊆ frontier A ∪ frontier B := by
  -- First, use the union lemma for the frontier.
  have h₁ :
      frontier ((A \ B) ∪ (B \ A)) ⊆
        frontier (A \ B) ∪ frontier (B \ A) :=
    Topology.frontier_union_subset (A := A \ B) (B := B \ A)
  -- Next, control each summand with the corresponding difference lemma.
  have h₂ : frontier (A \ B) ⊆ frontier A ∪ frontier B :=
    Topology.frontier_diff_subset (A := A) (B := B)
  have h₃ : frontier (B \ A) ⊆ frontier A ∪ frontier B := by
    -- Swap the roles of `A` and `B` in the previous lemma.
    simpa [Set.union_comm] using
      (Topology.frontier_diff_subset (A := B) (B := A))
  -- Assemble the three inclusions.
  intro x hx
  have hx' : x ∈ frontier (A \ B) ∪ frontier (B \ A) := h₁ hx
  cases hx' with
  | inl hA =>
      exact h₂ hA
  | inr hB =>
      exact h₃ hB



theorem Topology.closure_interior_diff_interior_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior (closure A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClosInt, hxNotIntClos⟩
  -- From `x ∈ closure (interior A)` we deduce `x ∈ closure A`.
  have hxClosA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hxClosInt
  -- Since `interior A ⊆ interior (closure A)`, the non-membership
  -- `x ∉ interior (closure A)` implies `x ∉ interior A`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hxIntA
    exact hxNotIntClos this
  -- Assemble the two facts to obtain `x ∈ frontier A`.
  exact And.intro hxClosA hxNotIntA

theorem Topology.interior_inter_closure_subset_closure_inter {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior A ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClosB⟩
  -- Prove the membership in the closure via the neighbourhood characterization.
  have h : ∀ U, IsOpen U → x ∈ U → (U ∩ (A ∩ B)).Nonempty := by
    intro U hU hxU
    -- The open set `U ∩ interior A` still contains `x`.
    have hV_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
    have hxV : x ∈ U ∩ interior A := ⟨hxU, hxIntA⟩
    -- Since `x ∈ closure B`, this open set meets `B`.
    have hNon : ((U ∩ interior A) ∩ B).Nonempty :=
      (mem_closure_iff.1 hxClosB) (U ∩ interior A) hV_open hxV
    rcases hNon with ⟨y, ⟨⟨hyU, hyIntA⟩, hyB⟩⟩
    -- The point `y` lies in `A` because it lies in `interior A`.
    have hyA : y ∈ A := interior_subset hyIntA
    -- Hence `y ∈ U ∩ (A ∩ B)`.
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact (mem_closure_iff).2 h

theorem Topology.closure_union_left_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) :
    closure (A ∪ B) = A ∪ closure B := by
  simpa [closure_union, hA.closure_eq]

theorem Topology.isOpen_closure_iff_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure A) ↔ interior (closure A) = closure A := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have hOpenInt : IsOpen (interior (closure A)) := isOpen_interior
    simpa [hEq] using hOpenInt

theorem Topology.P2_iff_frontier_subset_closure_interior_and_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) ↔
      (frontier A ⊆ closure (interior A) ∧ A ⊆ interior (closure A)) := by
  constructor
  · intro hP2
    have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
    have hP3 : Topology.P3 (A := A) := Topology.P2_implies_P3 (A := A) hP2
    have hFront :
        frontier A ⊆ closure (interior A) :=
      (Topology.P1_iff_frontier_subset_closure_interior (A := A)).1 hP1
    exact And.intro hFront hP3
  · rintro ⟨hFront, hSub⟩
    have hP1 : Topology.P1 (A := A) :=
      (Topology.P1_iff_frontier_subset_closure_interior (A := A)).2 hFront
    have hP3 : Topology.P3 (A := A) := hSub
    exact
      (Topology.P2_iff_P1_and_P3 (A := A)).2
        ⟨hP1, hP3⟩

theorem Topology.frontier_eq_empty_iff_closure_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = (∅ : Set X) ↔ closure A = interior A := by
  constructor
  · intro hFront
    -- Start from `interior A ∪ frontier A = closure A`
    have hUnion := Topology.interior_union_frontier_eq_closure (A := A)
    -- Replace `frontier A` with `∅`
    have h' : interior A ∪ (∅ : Set X) = closure A := by
      simpa [hFront] using hUnion
    -- Simplify the left‐hand side
    have hEq : interior A = closure A := by
      simpa [Set.union_empty] using h'
    -- Reorient equality
    simpa using hEq.symm
  · intro hEq
    exact
      Topology.frontier_eq_empty_of_closure_eq_interior
        (A := A) hEq

theorem Topology.frontier_eq_empty_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 (A := A)) :
    frontier A = (∅ : Set X) := by
  -- `P3` together with `A` closed implies `A` is open
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  -- A set that is both open and closed has empty frontier
  exact Topology.frontier_eq_empty_of_isOpen_and_isClosed
      (A := A) hOpen hA

theorem Topology.closure_eq_univ_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (Set.univ : Set X) ↔ interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro h
    exact
      Topology.interior_closure_eq_univ_of_closure_eq_univ
        (X := X) (A := A) h
  · intro h
    exact
      Topology.closure_eq_univ_of_interior_closure_eq_univ
        (X := X) (A := A) h

theorem Topology.isClosed_iff_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (A : Set X) ↔ frontier A ⊆ A := by
  constructor
  · intro hClosed
    exact Topology.frontier_subset_of_isClosed (A := A) hClosed
  · intro hSubset
    exact Topology.isClosed_of_frontier_subset (A := A) hSubset

theorem Topology.closure_closure_union_closure_eq_closure_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ closure B) = closure (A ∪ B) := by
  calc
    closure (closure A ∪ closure B)
        = closure (closure A) ∪ closure (closure B) := by
          simpa [closure_union]
    _ = closure A ∪ closure B := by
          simp [closure_closure]
    _ = closure (A ∪ B) := by
          simpa [closure_union]

theorem Topology.frontier_eq_closure_compl_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : closure A = (Set.univ : Set X)) :
    frontier A = closure (Aᶜ) := by
  calc
    frontier A = closure A ∩ closure (Aᶜ) := by
      simpa using
        (Topology.closure_inter_closure_compl_eq_frontier (X := X) (A := A)).symm
    _ = (Set.univ : Set X) ∩ closure (Aᶜ) := by
      simpa [hDense]
    _ = closure (Aᶜ) := by
      simp

theorem Topology.frontier_subset_of_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : closure A ⊆ B) :
    frontier A ⊆ B := by
  intro x hx
  exact h hx.1

theorem Topology.frontier_inter_eq_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : (A : Set X) ∩ frontier A = A \ interior A := by
  ext x
  constructor
  · intro hx
    have hA : x ∈ A := hx.1
    have hNotInt : x ∉ interior A := (hx.2).2
    exact And.intro hA hNotInt
  · intro hx
    have hA : x ∈ A := hx.1
    have hNotInt : x ∉ interior A := hx.2
    have hClos : x ∈ closure A := subset_closure hA
    have hFront : x ∈ frontier A := And.intro hClos hNotInt
    exact And.intro hA hFront

theorem Topology.closure_subset_closure_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ⊆ closure (A ∪ B) := by
  intro x hx
  have hIncl : (A : Set X) ⊆ A ∪ B := by
    intro y hy
    exact Or.inl hy
  exact (closure_mono hIncl) hx

theorem Topology.closure_inter_closure_subset_inter_closure₁
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- First, show `x ∈ closure A`.
  have hxA : x ∈ closure A := by
    have hSub : (A ∩ closure B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hx
  -- Next, show `x ∈ closure B`.
  have hxB : x ∈ closure B := by
    have hSub : (A ∩ closure B : Set X) ⊆ closure B := fun y hy => hy.2
    -- This gives `x ∈ closure (closure B)`, which simplifies to `closure B`.
    have : x ∈ closure (closure B) := (closure_mono hSub) hx
    simpa [closure_closure] using this
  exact And.intro hxA hxB

theorem Topology.interior_compl_eq_empty_of_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (Set.univ : Set X) → interior (Aᶜ) = (∅ : Set X) := by
  intro hDense
  apply Set.Subset.antisymm
  · intro x hxInt
    -- `interior (Aᶜ)` is an open neighbourhood of `x`
    have hOpen : IsOpen (interior (Aᶜ)) := isOpen_interior
    -- Since `closure A = univ`, we have `x ∈ closure A`
    have hxClos : x ∈ closure A := by
      simpa [hDense] using (Set.mem_univ x)
    -- Therefore this open neighbourhood meets `A`
    have hNon :
        ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClos (interior (Aᶜ)) hOpen hxInt
    rcases hNon with ⟨y, ⟨hyIntCompl, hyA⟩⟩
    -- But `y ∈ interior (Aᶜ)` implies `y ∉ A`, contradiction
    have : (y : X) ∈ Aᶜ :=
      (interior_subset : interior (Aᶜ) ⊆ Aᶜ) hyIntCompl
    exact (this hyA).elim
  ·
    intro x hx
    cases hx

theorem Topology.interior_inter_interior_eq_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ interior B) = interior A ∩ interior B := by
  -- `interior B` is open, so we can apply the general lemma
  have hOpen : IsOpen (interior B) := isOpen_interior
  simpa [interior_interior] using
    (Topology.interior_inter_eq_inter_left_of_isOpen_right
      (A := A) (B := interior B) hOpen)

theorem Topology.P2_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P2 (A := A) := by
  intro hDense
  dsimp [Topology.P2]
  intro x _
  -- Since `closure (interior A) = univ`, its interior is also `univ`.
  have hInt : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [hDense, interior_univ]
  -- Any point `x` lies in `univ`, hence in the required interior.
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    exact Set.mem_univ x
  simpa [hInt] using hx_univ

theorem Topology.closure_diff_interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) →
      closure A \ interior (closure A) ⊆ closure (interior A) := by
  intro hP1
  intro x hx
  have hxClos : x ∈ closure A := hx.1
  have hSub : closure A ⊆ closure (interior A) :=
    Topology.closure_subset_closure_interior_of_P1 (A := A) hP1
  exact hSub hxClos

theorem Topology.interiors_disjoint {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hIntA, hIntAc⟩
    have hA : x ∈ A := interior_subset hIntA
    have hAc : x ∈ Aᶜ := interior_subset hIntAc
    exact (hAc hA).elim
  · exact Set.empty_subset _

theorem Topology.closure_union_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B) := hA.union hB
  simpa using hClosed.closure_eq



theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  have hEq :=
    Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
      (X := X) (A := A)
  have : x ∈ closure (interior (closure (interior (closure A)))) := by
    simpa [hEq] using hx
  exact this

theorem Topology.interior_union_interior_compl_union_frontier_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∪ interior (Aᶜ) ∪ frontier A = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    by_cases h : x ∈ interior A ∪ interior (Aᶜ)
    · exact Or.inl h
    ·
      have hFront :
          frontier A = (interior A ∪ interior (Aᶜ))ᶜ :=
        Topology.frontier_eq_compl_interior_union_interior_compl (A := A)
      have hxFront : x ∈ frontier A := by
        have hxComp : x ∈ (interior A ∪ interior (Aᶜ))ᶜ := by
          simpa [Set.mem_compl] using h
        simpa [hFront] using hxComp
      exact Or.inr hxFront

theorem Topology.interior_closure_diff_closure_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ closure (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxIntClos, hxNotClosInt⟩
  -- `x ∈ closure A` because `interior (closure A) ⊆ closure A`.
  have hxClosA : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
  -- We show `x ∉ interior A` using the assumption `x ∉ closure (interior A)`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : x ∈ closure (interior A) := subset_closure hxIntA
    exact hxNotClosInt this
  -- Assemble the two facts to obtain membership in the frontier.
  exact And.intro hxClosA hxNotIntA

theorem Topology.closure_interior_diff_interior_closure_subset_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior (closure A) ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxClosIntA, hxNotIntClosA⟩
  -- `x ∈ closure A` since `closure (interior A) ⊆ closure A`
  have hxClosA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hxClosIntA
  -- Show `x ∉ interior A` using the assumption `x ∉ interior (closure A)`
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hxIntA
    exact hxNotIntClosA this
  exact And.intro hxClosA hxNotIntA

theorem Topology.frontier_eq_closure_of_empty_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hInt : interior A = (∅ : Set X)) :
    frontier A = closure A := by
  simpa [frontier, hInt]

theorem Topology.subset_interior_union_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X) ⊆ interior A ∪ frontier A := by
  intro x hxA
  by_cases hInt : x ∈ interior A
  · exact Or.inl hInt
  ·
    have hClos : x ∈ closure A := subset_closure hxA
    exact Or.inr ⟨hClos, hInt⟩

theorem Topology.closure_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) ⊆ closure A := by
  -- `frontier A` is closed, so its closure is itself.
  have hEq : closure (frontier A) = frontier A :=
    Topology.closure_frontier_eq_frontier (A := A)
  -- The frontier of `A` is always contained in `closure A`.
  have hSubset : (frontier A : Set X) ⊆ closure A :=
    Topology.frontier_subset_closure (A := A)
  -- Combine the two facts.
  simpa [hEq] using hSubset

theorem Topology.open_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) : (A : Set X) ⊆ interior (closure A) := by
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  exact interior_maximal hSub hA

theorem Topology.diff_interior_subset_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    A \ interior A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxA, hxNotInt⟩
  have hxClos : x ∈ closure A := subset_closure hxA
  exact And.intro hxClos hxNotInt

theorem Topology.P2_of_frontier_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) → Topology.P2 (A := A) := by
  intro hFrontier
  have hOpen : IsOpen (A : Set X) :=
    ((Topology.frontier_eq_empty_iff_isOpen_and_isClosed (A := A)).1 hFrontier).1
  exact Topology.P2_of_isOpen (A := A) hOpen

theorem Topology.interior_inter_closure_subset_interior_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ closure B) ⊆ interior A := by
  intro x hx
  -- Since `A ∩ closure B ⊆ A`, monotonicity of `interior` yields the result.
  have hSub : (A ∩ closure B : Set X) ⊆ A := fun y hy => hy.1
  exact (interior_mono hSub) hx



theorem Topology.frontier_eq_closure_inter_compl_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    frontier A = closure A ∩ Aᶜ := by
  have h := Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA
  simpa [Set.diff_eq] using h

theorem Topology.P1_iff_subset_closure_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (A := A) ↔ (A ⊆ closure (interior A)) := by
  simpa [hA.closure_eq] using
    (Topology.P1_iff_closure_subset_closure_interior
      (X := X) (A := A))

theorem Topology.frontier_subset_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure A ∩ closure (Aᶜ) := by
  intro x hx
  have h₁ : x ∈ closure A :=
    (Topology.frontier_subset_closure (A := A)) hx
  have h₂ : x ∈ closure (Aᶜ) :=
    (Topology.frontier_subset_closure_compl (A := A)) hx
  exact And.intro h₁ h₂

theorem Topology.interior_inter_closure_subset_interior_and_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure B) ⊆ interior A ∩ closure B := by
  intro x hx
  -- From an existing lemma we get `x ∈ interior A`.
  have hxIntA : x ∈ interior A :=
    (Topology.interior_inter_closure_subset_interior_left
        (A := A) (B := B)) hx
  -- Since `x` lies in `interior (A ∩ closure B)`, it also lies in `A ∩ closure B`.
  have hSub : (interior (A ∩ closure B) : Set X) ⊆ A ∩ closure B :=
    interior_subset
  have hxAC : x ∈ A ∩ closure B := hSub hx
  -- Extract the membership in `closure B`.
  have hxClosB : x ∈ closure B := hxAC.2
  exact And.intro hxIntA hxClosB



theorem Topology.P1_of_frontier_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) → Topology.P1 (A := A) := by
  intro hFrontier
  -- Since `frontier A = ∅`, it is trivially included in any set.
  have hSub : frontier A ⊆ closure (interior A) := by
    intro x hx
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hFrontier] using hx
    cases this
  -- Use the characterization of `P1` via the frontier.
  exact
    (Topology.P1_iff_frontier_subset_closure_interior
      (X := X) (A := A)).2 hSub

theorem Topology.open_inter_frontier_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    (A ∩ frontier A : Set X) = (∅ : Set X) := by
  -- First show that `A ∩ frontier A` is empty.
  have hSub : (A ∩ frontier A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    rcases hx with ⟨hxA, hxFront⟩
    -- For an open set `A`, the frontier is contained in the complement of `A`.
    have hFrontSub : frontier A ⊆ Aᶜ :=
      Topology.frontier_subset_compl_of_isOpen (A := A) hA
    -- Hence `x ∈ Aᶜ`, contradicting `x ∈ A`.
    have : x ∈ Aᶜ := hFrontSub hxFront
    exact (this hxA).elim
  -- The reverse inclusion is trivial.
  have hEmptySub : (∅ : Set X) ⊆ (A ∩ frontier A : Set X) := by
    intro x hx
    cases hx
  -- Combine the two inclusions to get the desired equality of sets.
  exact Set.Subset.antisymm hSub hEmptySub

theorem Topology.P3_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    Topology.P3 (A := A) → A ⊆ interior (closure B) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  intro x hxA
  -- Step 1: `x ∈ interior (closure A)` by `P3` for `A`.
  have hxIntClosA : x ∈ interior (closure A) := hP3 hxA
  -- Step 2: Use monotonicity of `closure` and `interior` with `A ⊆ B`.
  have hClos : closure A ⊆ closure B := closure_mono hAB
  have hIntMono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono hClos
  -- Step 3: Conclude the desired membership.
  exact hIntMono hxIntClosA

theorem Topology.frontier_union_subset_closure_frontier_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B) ⊆ closure (frontier A ∪ frontier B) := by
  intro x hx
  have hx_union : x ∈ frontier A ∪ frontier B :=
    (Topology.frontier_union_subset (A := A) (B := B)) hx
  exact subset_closure hx_union

theorem Topology.frontier_eq_closure_inter_compl_of_isOpen' {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    frontier A = closure A ∩ Aᶜ := by
  have h := Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA
  simpa [Set.diff_eq] using h

theorem Topology.frontier_closure_interior_subset_frontier {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier (closure (interior A)) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClos, hxNotInt⟩
  -- `hxClos` lives in `closure (closure (interior A))`, simplify the double closure
  have hxClosInt : x ∈ closure (interior A) := by
    simpa [closure_closure] using hxClos
  -- From the monotonicity of `closure`, obtain `x ∈ closure A`
  have hxClosA : x ∈ closure A := by
    have hSub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (A := A)
    exact hSub hxClosInt
  -- Show that `x ∉ interior A`; otherwise we contradict `hxNotInt`
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have hSubInt :
        interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    have : x ∈ interior (closure (interior A)) := hSubInt hxIntA
    exact hxNotInt this
  -- Assemble the two facts to conclude `x ∈ frontier A`
  exact And.intro hxClosA hxNotIntA

theorem Topology.closure_interior_inter_frontier_closure_eq_closure_interior_diff_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ frontier (closure A) =
      closure (interior A) \ interior (closure A) := by
  -- First, rewrite the frontier of a closed set.
  have hFront :
      frontier (closure A) =
        closure A \ interior (closure A) := by
    simp [frontier, closure_closure]
  -- We now identify the desired equality by set‐extensionality.
  ext x
  constructor
  · intro hx
    -- Decompose the membership in the intersection.
    rcases hx with ⟨hxClosInt, hxDiff⟩
    -- `hxDiff` witnesses `x ∈ closure A ∧ x ∉ interior (closure A)`.
    exact And.intro hxClosInt hxDiff.2
  · intro hx
    rcases hx with ⟨hxClosInt, hxNotIntClos⟩
    -- From `x ∈ closure (interior A)` we infer `x ∈ closure A`.
    have hxClosA : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (A := A)) hxClosInt
    -- Assemble the data to obtain membership in the original intersection.
    have hxDiff : x ∈ closure A \ interior (closure A) :=
      And.intro hxClosA hxNotIntClos
    -- Conclude the required membership.
    have : x ∈ closure (interior A) ∩ (closure A \ interior (closure A)) :=
      And.intro hxClosInt hxDiff
    -- Rewrite back using `hFront`.
    simpa [hFront] using this

theorem Topology.interior_closure_inter_frontier_eq_interior_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∩ frontier A =
      interior (closure A) \ interior A := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxIntClos, hxFront⟩
    exact ⟨hxIntClos, hxFront.2⟩
  · intro hx
    rcases hx with ⟨hxIntClos, hxNotIntA⟩
    have hxClosA : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
    have hxFront : x ∈ frontier A := And.intro hxClosA hxNotIntA
    exact And.intro hxIntClos hxFront

theorem Topology.closure_diff_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- We prove the closure condition via neighbourhoods.
  have h :
      ∀ U, IsOpen U → x ∈ U → ((U ∩ (A \ B) : Set X)).Nonempty := by
    intro U hU hxU
    -- Intersect `U` with the open complement of `closure B`.
    let W : Set X := U ∩ (closure B)ᶜ
    have hW_open : IsOpen W :=
      hU.inter ((isClosed_closure (s := B)).isOpen_compl)
    have hxW : x ∈ W := by
      have hxComp : x ∈ (closure B)ᶜ := hxNotB
      exact And.intro hxU hxComp
    -- Since `x ∈ closure A`, `W ∩ A` is nonempty.
    have hNon : ((W ∩ A : Set X)).Nonempty :=
      (mem_closure_iff.1 hxA) W hW_open hxW
    rcases hNon with ⟨y, ⟨⟨hyU, hyComp⟩, hyA⟩⟩
    -- `y ∉ B` because `y ∈ (closure B)ᶜ ⊆ Bᶜ`.
    have hyNotB : y ∉ B := by
      intro hyB
      have : (y : X) ∈ closure B := subset_closure hyB
      exact hyComp this
    -- Thus, `y ∈ U ∩ (A \ B)`.
    exact ⟨y, ⟨hyU, And.intro hyA hyNotB⟩⟩
  exact (mem_closure_iff.2 h)

theorem Topology.closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A ∪ interior A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hClos => exact hClos
    | inr hInt =>
        have : (x : X) ∈ A := interior_subset hInt
        exact subset_closure this
  · intro x hx
    exact Or.inl hx

theorem Topology.closure_inter_subset_left_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) :
    closure (A ∩ B) ⊆ A ∩ closure B := by
  intro x hx
  -- First, use the general inclusion into the intersection of closures.
  have h := (Topology.closure_inter_subset_inter_closure (A := A) (B := B)) hx
  -- Since `A` is closed, `closure A = A`, so we can refine the left component.
  have hxA : x ∈ A := by
    simpa [hA.closure_eq] using h.1
  -- The right component is already the required `x ∈ closure B`.
  exact And.intro hxA h.2

theorem Topology.closure_eq_self_iff_isClosed {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = A ↔ IsClosed A := by
  constructor
  · intro hEq
    have hClosed : IsClosed (closure A) := isClosed_closure (s := A)
    simpa [hEq] using hClosed
  · intro hClosed
    simpa using hClosed.closure_eq

theorem Topology.frontier_frontier_subset_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (frontier A) ⊆ closure A ∩ closure (Aᶜ) := by
  intro x hx
  have hxFrontA : x ∈ frontier A :=
    (Topology.frontier_frontier_subset_frontier (A := A)) hx
  exact (Topology.frontier_subset_closure_inter_closure_compl (A := A)) hxFrontA

theorem Topology.closure_frontier_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) = closure A ∩ closure (Aᶜ) := by
  -- `frontier A` is closed, so its closure is itself
  have h₁ : closure (frontier A) = frontier A :=
    Topology.closure_frontier_eq_frontier (A := A)
  -- The frontier can be expressed as the intersection of the two closures
  have h₂ : frontier A = closure A ∩ closure (Aᶜ) :=
    (Topology.closure_inter_closure_compl_eq_frontier (A := A)).symm
  -- Combine the two equalities
  simpa [h₁] using h₂

theorem Topology.interior_union_closure_eq_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A ∪ closure A) = interior (closure A) := by
  have hUnion : (A ∪ closure A : Set X) = closure A := by
    have hSub : (A : Set X) ⊆ closure A := subset_closure
    simpa [Set.union_eq_right.2 hSub]
  simpa [hUnion]

theorem Topology.closure_compl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (Aᶜ) ∩ interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxClosCompl, hxIntA⟩
    -- `interior A` is an open neighbourhood of `x` contained in `A`.
    have hNon :
        ((interior A : Set X) ∩ Aᶜ).Nonempty :=
      (mem_closure_iff).1 hxClosCompl (interior A) isOpen_interior hxIntA
    rcases hNon with ⟨y, ⟨hyIntA, hyCompl⟩⟩
    -- The point `y` lies both in `A` and `Aᶜ`, a contradiction.
    have : (y : X) ∈ A := interior_subset hyIntA
    exact (hyCompl this).elim
  · intro x hx
    cases hx

theorem Topology.interior_closure_inter_mono_left
    {X : Type*} [TopologicalSpace X] {A B C : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (A ∩ C)) ⊆ interior (closure (B ∩ C)) := by
  intro x hx
  -- First, upgrade the inclusion `(A ∩ C) ⊆ (B ∩ C)` to closures.
  have hClos : closure (A ∩ C) ⊆ closure (B ∩ C) := by
    have hSub : (A ∩ C : Set X) ⊆ B ∩ C := by
      intro y hy
      exact And.intro (hAB hy.1) hy.2
    exact closure_mono hSub
  -- Then apply monotonicity of `interior` to conclude.
  exact (interior_mono hClos) hx

theorem Topology.disjoint_interior_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (interior A) (frontier A) := by
  have h :=
    Topology.interior_inter_frontier_eq_empty (X := X) (A := A)
  simpa [Set.disjoint_iff_inter_eq_empty] using h

theorem Topology.closure_interior_inter_closure_interior_compl_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ closure (interior (Aᶜ)) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hClosIntA, hClosIntAc⟩
  -- `x` lies in `closure A` because `closure (interior A) ⊆ closure A`.
  have hClosA : x ∈ closure A := by
    have hSub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (A := A)
    exact hSub hClosIntA
  -- Show that `x ∉ interior A`; otherwise we obtain a contradiction.
  have hNotIntA : x ∉ interior A := by
    intro hxIntA
    -- `interior A` is an open neighbourhood of `x`; since
    -- `x ∈ closure (interior (Aᶜ))`, this neighbourhood meets `interior (Aᶜ)`.
    have hNon :
        ((interior A : Set X) ∩ interior (Aᶜ)).Nonempty :=
      (mem_closure_iff).1 hClosIntAc (interior A) isOpen_interior hxIntA
    rcases hNon with ⟨y, ⟨hyIntA, hyIntAc⟩⟩
    -- But a point cannot belong to both `A` and `Aᶜ`.
    have hInA  : (y : X) ∈ A   := interior_subset hyIntA
    have hInAc : (y : X) ∈ Aᶜ := interior_subset hyIntAc
    exact (hInAc hInA)
  exact And.intro hClosA hNotIntA

theorem Topology.frontier_interior_subset_closure_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior A) ⊆ closure (frontier A) := by
  intro x hx
  -- First, move from the frontier of `interior A` to the frontier of `A`.
  have hFrontA : x ∈ frontier A :=
    (Topology.frontier_interior_subset_frontier (A := A)) hx
  -- Then use the fact that every set is contained in the closure of itself.
  exact (subset_closure : frontier A ⊆ closure (frontier A)) hFrontA

theorem Topology.closure_closed_right_inter_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    closure A ∩ closure B = closure A ∩ B := by
  simpa [Set.inter_comm, Set.inter_left_comm] using
    (Topology.closure_closed_left_inter_eq (X := X) (A := B) (B := A) hB)

theorem Topology.interior_closure_subset_closure_interior_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior A) ∪ frontier A := by
  intro x hxInt
  by_cases h : x ∈ closure (interior A)
  · exact Or.inl h
  ·
    -- If `x ∉ closure (interior A)`, then it lies in the set difference
    have hxDiff : x ∈ interior (closure A) \ closure (interior A) :=
      And.intro hxInt h
    -- The previously proved lemma sends this difference into the frontier
    have hxFront :
        x ∈ frontier A :=
      (Topology.interior_closure_diff_closure_interior_subset_frontier
        (A := A)) hxDiff
    exact Or.inr hxFront

theorem Topology.closure_interior_subset_self_union_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ⊆ A ∪ frontier A := by
  intro x hx
  by_cases hInt : x ∈ interior A
  · exact Or.inl (interior_subset hInt)
  ·
    have hClosA : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (A := A)) hx
    have hFront : x ∈ frontier A := And.intro hClosA hInt
    exact Or.inr hFront

theorem Topology.closure_interior_closure_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → closure (interior (closure A)) = closure A := by
  intro hP1
  -- First, rewrite `closure (interior (closure A))` using `P1`.
  have h₁ :=
    Topology.closure_interior_closure_eq_closure_interior_of_P1
      (X := X) (A := A) hP1
  -- Secondly, `P1` identifies `closure A` with `closure (interior A)`.
  have h₂ :=
    Topology.closure_eq_closure_interior_of_P1
      (X := X) (A := A) hP1
  -- Combine the two equalities.
  calc
    closure (interior (closure A))
        = closure (interior A) := h₁
    _ = closure A := by
          simpa using h₂.symm

theorem Topology.closure_frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    closure (frontier A) ⊆ A := by
  -- First, we know the frontier itself is contained in `A`.
  have hSub : frontier A ⊆ A :=
    Topology.frontier_subset_of_isClosed (A := A) hA
  -- Taking closures preserves inclusions.
  have hClosSub : closure (frontier A) ⊆ closure A :=
    closure_mono hSub
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using hClosSub

theorem Topology.not_P1_of_empty_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hInt : interior A = (∅ : Set X)) (hNon : A.Nonempty) :
    ¬ Topology.P1 (A := A) := by
  intro hP1
  rcases hNon with ⟨x, hxA⟩
  have hx : x ∈ closure (interior A) := hP1 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hInt, closure_empty] using hx
  cases this

theorem Topology.closure_diff_union_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ (A ∪ frontier A) = (∅ : Set X) := by
  have hUnion : (A : Set X) ∪ frontier A = closure A :=
    (Topology.closure_eq_self_union_frontier (A := A)).symm
  calc
    closure A \ (A ∪ frontier A)
        = closure A \ closure A := by
          simpa [hUnion]
    _ = (∅ : Set X) := by
          simp

theorem Topology.frontier_eq_closure_inter_compl_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = closure A ∩ (interior A)ᶜ := by
  simpa [frontier, Set.diff_eq]

theorem Topology.isClosed_closure_union_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsClosed (closure A ∪ closure B) := by
  have hA : IsClosed (closure A) := isClosed_closure
  have hB : IsClosed (closure B) := isClosed_closure
  exact hA.union hB

theorem Topology.closure_frontier_subset_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) ⊆ closure (Aᶜ) := by
  -- First, use the established inclusion for the frontier itself.
  have hSub : (frontier A : Set X) ⊆ closure (Aᶜ) :=
    Topology.frontier_subset_closure_compl (A := A)
  -- Taking closures preserves set inclusion.
  have hClos : closure (frontier A) ⊆ closure (closure (Aᶜ)) :=
    closure_mono hSub
  -- Simplify the double closure on the right.
  simpa [closure_closure] using hClos

theorem Topology.interior_closure_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxIntClos, hxIntCompl⟩
    -- `x` also lies in `closure A`
    have hxClos : (x : X) ∈ closure A := interior_subset hxIntClos
    -- Hence `x` lies in the already‐known empty intersection
    have hxIn : x ∈ closure A ∩ interior (Aᶜ) :=
      And.intro hxClos hxIntCompl
    -- But this intersection is empty
    have hEmpty :
        (closure A ∩ interior (Aᶜ) : Set X) = (∅ : Set X) :=
      Topology.closure_inter_interior_compl_eq_empty (A := A)
    have : x ∈ (∅ : Set X) := by
      simpa [hEmpty] using hxIn
    cases this
  · exact Set.empty_subset _

theorem Topology.interior_closure_inter_interior_subset_interior_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆ interior (closure (A ∩ B)) := by
  intro x hx
  -- Step 1:  `(A ∩ interior B) ⊆ (A ∩ B)`
  have hSub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro y hy
    exact And.intro hy.1 (interior_subset hy.2)
  -- Step 2:  Take closures on both sides of the inclusion.
  have hClos : closure (A ∩ interior B) ⊆ closure (A ∩ B) :=
    closure_mono hSub
  -- Step 3:  Apply monotonicity of `interior`.
  exact (interior_mono hClos) hx

theorem Topology.closure_interior_inter_subset_inter_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  -- `interior A ∩ B` is contained in `interior A`
  have hSubIntA : (interior A ∩ B : Set X) ⊆ interior A := fun y hy => hy.1
  -- `interior A ∩ B` is also contained in `B`
  have hSubB : (interior A ∩ B : Set X) ⊆ B := fun y hy => hy.2
  -- Monotonicity of `closure` gives the two required memberships
  have hxIntA : x ∈ closure (interior A) := (closure_mono hSubIntA) hx
  have hxB : x ∈ closure B := (closure_mono hSubB) hx
  exact And.intro hxIntA hxB

theorem Topology.frontier_inter_compl_eq_empty_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    frontier (A : Set X) ∩ Aᶜ = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxFront, hxCompl⟩
    have hxA : x ∈ A :=
      (Topology.frontier_subset_of_isClosed (A := A) hA) hxFront
    exact ((hxCompl : x ∉ A) hxA).elim
  · exact Set.empty_subset _



theorem Topology.P3_iff_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := A) ↔ A ⊆ interior (closure A) := by
  rfl

theorem Topology.interior_union_interiors_eq_union_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (interior A ∪ interior B) = interior A ∪ interior B := by
  have hOpen : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  simpa using hOpen.interior_eq

theorem Topology.frontier_subset_closure_union_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure A ∪ closure (Aᶜ) := by
  intro x hx
  have h₁ : x ∈ closure A :=
    (Topology.frontier_subset_closure (A := A)) hx
  exact Or.inl h₁

theorem Topology.frontier_eq_frontier_inter_closure_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) = frontier A ∩ closure (Aᶜ) := by
  ext x
  constructor
  · intro hx
    have h₁ : x ∈ closure (Aᶜ) :=
      (Topology.frontier_subset_closure_compl (A := A)) hx
    exact And.intro hx h₁
  · intro hx
    exact hx.1