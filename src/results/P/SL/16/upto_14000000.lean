

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hP2 x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact hsubset hx

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2 x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_closure_subset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  exact h_int_subset hx₁

theorem Topology.isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  exact interior_maximal subset_closure hA

theorem Topology.isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x hxA
  -- First, rewrite `hxA` as a membership in `interior A`
  have hxInt : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  -- Show that `interior A` is contained in `interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    have : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono subset_closure
    simpa [interior_interior] using this
  -- Conclude that `x ∈ interior (closure (interior A))`
  exact h_subset hxInt

theorem Topology.isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (X := X) A := by
  exact Topology.P2_implies_P1 (X := X) (A := A)
    (Topology.isOpen_implies_P2 (X := X) (A := A) hA)

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A := by
  intro hP2
  exact
    ⟨Topology.P2_implies_P1 (X := X) (A := A) hP2,
      Topology.P2_implies_P3 (X := X) (A := A) hP2⟩

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior A) hOpen

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior A) hOpen

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (X := X) A → Topology.P1 (X := X) B → Topology.P1 (X := X) (A ∪ B) := by
  intro hPA hPB
  dsimp [Topology.P1] at hPA hPB ⊢
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hx_closure_intA : x ∈ closure (interior A) := hPA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_interior_subset : interior A ⊆ interior (A ∪ B) := by
          -- `interior` is monotone, so it respects subset relations
          have hA_subset : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hA_subset
        exact h_interior_subset
      exact h_subset hx_closure_intA
  | inr hxB =>
      have hx_closure_intB : x ∈ closure (interior B) := hPB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_interior_subset : interior B ⊆ interior (A ∪ B) := by
          have hB_subset : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hB_subset
        exact h_interior_subset
      exact h_subset hx_closure_intB

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (X := X) A → Topology.P3 (X := X) B → Topology.P3 (X := X) (A ∪ B) := by
  intro hPA hPB
  dsimp [Topology.P3] at hPA hPB ⊢
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hPA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure_subset : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact interior_mono h_closure_subset
      exact h_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hPB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure_subset : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact interior_mono h_closure_subset
      exact h_subset hxB'

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (X := X) A → Topology.P2 (X := X) B → Topology.P2 (X := X) (A ∪ B) := by
  intro hPA hPB
  dsimp [Topology.P2] at hPA hPB ⊢
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hPA hxA
      have h_subset : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
        have h_closure_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int_subset : interior A ⊆ interior (A ∪ B) := by
            have hA_subset : A ⊆ A ∪ B := by
              intro y hy
              exact Or.inl hy
            exact interior_mono hA_subset
          exact h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hPB hxB
      have h_subset : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
        have h_closure_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int_subset : interior B ⊆ interior (A ∪ B) := by
            have hB_subset : B ⊆ A ∪ B := by
              intro y hy
              exact Or.inr hy
            exact interior_mono hB_subset
          exact h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hxB'

theorem Topology.empty_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) ∧
    Topology.P2 (X := X) (∅ : Set X) ∧
    Topology.P3 (X := X) (∅ : Set X) := by
  have hP1 : Topology.P1 (X := X) (∅ : Set X) := by
    dsimp [Topology.P1]
    intro x hx
    cases hx
  have hP2 : Topology.P2 (X := X) (∅ : Set X) := by
    dsimp [Topology.P2]
    intro x hx
    cases hx
  have hP3 : Topology.P3 (X := X) (∅ : Set X) := by
    dsimp [Topology.P3]
    intro x hx
    cases hx
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is contained in `interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    have : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono subset_closure
    simpa [interior_interior] using this
  -- Taking closures preserves this inclusion
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_subset
  exact h_closure_subset hx

theorem Topology.interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ interior (closure (interior A)) := by
  have h : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono subset_closure
  simpa [interior_interior] using h

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) : Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  simp [h_dense]

theorem Topology.P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior (closure A)) hOpen

theorem Topology.interior_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior A) ∧
    Topology.P2 (X := X) (interior A) ∧
    Topology.P3 (X := X) (interior A) := by
  exact
    ⟨Topology.P1_interior (X := X) (A := A),
      Topology.P2_interior (X := X) (A := A),
      Topology.P3_interior (X := X) (A := A)⟩

theorem Topology.interior_closure_interior_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) (interior (closure (interior A))) ∧
    Topology.P2 (X := X) (interior (closure (interior A))) ∧
    Topology.P3 (X := X) (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  have hP1 : Topology.P1 (X := X) (interior (closure (interior A))) :=
    Topology.isOpen_implies_P1 (X := X) (A := interior (closure (interior A))) hOpen
  have hP2 : Topology.P2 (X := X) (interior (closure (interior A))) :=
    Topology.isOpen_implies_P2 (X := X) (A := interior (closure (interior A))) hOpen
  have hP3 : Topology.P3 (X := X) (interior (closure (interior A))) :=
    Topology.isOpen_implies_P3 (X := X) (A := interior (closure (interior A))) hOpen
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) → Topology.P3 (X := X) A := by
  intro hP3Closure
  dsimp [Topology.P3] at hP3Closure ⊢
  intro x hxA
  have hxClosure : x ∈ closure A := subset_closure hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3Closure hxClosure
  simpa [closure_closure] using hxInt

theorem Topology.closed_P3_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 (X := X) A) : IsOpen A := by
  -- Since `A` is closed, its closure is itself.
  have h_closure : closure A = A := hClosed.closure_eq
  -- From `P3`, every point of `A` lies in `interior (closure A) = interior A`.
  have h_subset : A ⊆ interior A := by
    intro x hx
    have hxInt : x ∈ interior (closure A) := hP3 hx
    simpa [h_closure] using hxInt
  -- We already have `interior A ⊆ A`, so the two sets are equal.
  have h_eq : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    · exact h_subset
  -- The interior of any set is open; rewrite with the equality to conclude.
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa [h_eq] using h_open

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure A)) := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure (interior (closure A)) := subset_closure hx
  simpa [interior_interior] using this

theorem Topology.closed_P3_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P3 (X := X) A ↔ IsOpen A := by
  constructor
  · intro hP3
    exact Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  · intro hOpen
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem Topology.P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior (closure A)) hOpen

theorem Topology.closed_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  have hOpen : IsOpen A := Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem Topology.closed_P1_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = A := by
  apply subset_antisymm
  · have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    simpa [hClosed.closure_eq] using h_subset
  · intro x hxA
    exact hP1 hxA

theorem Topology.closed_P1_iff_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    Topology.P1 (X := X) A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closed_P1_closure_interior_eq_self (X := X) (A := A) hClosed hP1
  · intro h_eq
    -- Prove `P1` using the assumed equality
    dsimp [Topology.P1]
    intro x hxA
    have : x ∈ closure (interior A) := by
      simpa [h_eq] using hxA
    exact this

theorem Topology.closed_P2_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) :
    IsOpen A := by
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3

theorem Topology.closed_P2_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P2 (X := X) A ↔ IsOpen A := by
  constructor
  · intro hP2
    exact Topology.closed_P2_isOpen (X := X) (A := A) hClosed hP2
  · intro hOpen
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem Topology.closed_P3_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) A := by
  have hOpen : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h : interior (closure (interior A)) ⊆ closure (interior A) := by
      simpa using (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
    have h' : closure (interior (closure (interior A))) ⊆
        closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using h'
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (X := X) (A := A)
    have h' : closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h
    exact h'

theorem Topology.P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  have hxClosure : x ∈ closure A := subset_closure hxA
  have hInt : interior (closure A) = closure A := hOpen.interior_eq
  simpa [hInt] using hxClosure

theorem Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa [Topology.closure_interior_closure_interior_eq_closure_interior (X := X) (A := A)]

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem Topology.closed_P2_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) :
    closure (interior A) = A := by
  -- From `P2` and closedness we know `A` is open
  have hOpen : IsOpen A := Topology.closed_P2_isOpen (X := X) (A := A) hClosed hP2
  -- Hence `interior A = A`
  have hInt : interior A = A := hOpen.interior_eq
  -- And `closure A = A`
  have hCl : closure A = A := hClosed.closure_eq
  -- Putting these equalities together
  calc
    closure (interior A) = closure A := by
      simpa [hInt]
    _ = A := by
      simpa [hCl]

theorem Topology.closed_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  have h₁ := Topology.closed_P2_iff_isOpen (X := X) (A := A) hClosed
  have h₂ := Topology.closed_P3_iff_isOpen (X := X) (A := A) hClosed
  exact h₁.trans h₂.symm

theorem Topology.univ_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) ∧
    Topology.P2 (X := X) (Set.univ : Set X) ∧
    Topology.P3 (X := X) (Set.univ : Set X) := by
  -- Prove `P1`.
  have hP1 : Topology.P1 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P1]
    intro x hx
    simpa [closure_univ, interior_univ] using hx
  -- Prove `P2`.
  have hP2 : Topology.P2 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P2]
    intro x hx
    simpa [closure_univ, interior_univ] using hx
  -- Prove `P3`.
  have hP3 : Topology.P3 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P3]
    intro x hx
    simpa [closure_univ, interior_univ] using hx
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.closure_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = closure A := by
  apply subset_antisymm
  · -- `closure (interior A) ⊆ closure A` by monotonicity of `closure`
    exact closure_mono (interior_subset : interior A ⊆ A)
  · -- For the reverse inclusion use `A ⊆ closure (interior A)` from `P1`
    have h : A ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using this

theorem Topology.closure_interior_inter_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have h_int_subset_left : interior (A ∩ B) ⊆ interior A :=
    interior_mono Set.inter_subset_left
  have h_int_subset_right : interior (A ∩ B) ⊆ interior B :=
    interior_mono Set.inter_subset_right
  have hx_left : x ∈ closure (interior A) :=
    (closure_mono h_int_subset_left) hx
  have hx_right : x ∈ closure (interior B) :=
    (closure_mono h_int_subset_right) hx
  exact ⟨hx_left, hx_right⟩

theorem Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := closure A))

theorem Topology.closure_interior_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → closure (interior A) = closure A := by
  intro hP2
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1

theorem Topology.P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  · intro h_eq
    dsimp [Topology.P1]
    intro x hxA
    have hxCl : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hxCl

theorem Topology.closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_int_subset : interior A ⊆ interior (A ∪ B) := by
        have h_sub : A ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact interior_mono h_sub
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hxA
  | inr hxB =>
      have h_int_subset : interior B ⊆ interior (A ∪ B) := by
        have h_sub : B ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono h_sub
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hxB

theorem Topology.interior_closure_interior_eq_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    interior (closure (interior A)) = interior (closure A) := by
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  simpa [h_eq]

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem Topology.closed_P3_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hP3A : Topology.P3 (X := X) A) (hP3B : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∩ B) := by
  -- From `hAclosed` and `hP3A`, `A` is open.
  have hOpenA : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hAclosed hP3A
  -- From `hBclosed` and `hP3B`, `B` is open.
  have hOpenB : IsOpen B :=
    Topology.closed_P3_isOpen (X := X) (A := B) hBclosed hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A ∩ B) hOpenInter

theorem Topology.isOpen_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  -- Since `A` is open, it satisfies both `P2` and `P3`.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hOpen
  have hP3 : Topology.P3 (X := X) A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hOpen
  constructor
  · intro _; exact hP3
  · intro _; exact hP2

theorem Topology.interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Use monotonicity of `closure` to obtain the required inclusion.
      have h_closure_subset : closure A ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      -- Apply `interior_mono` to get the inclusion on interiors.
      have h_int_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_subset
      exact h_int_subset hxA
  | inr hxB =>
      have h_closure_subset : closure B ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      have h_int_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_subset
      exact h_int_subset hxB

theorem Topology.interior_closure_inter_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    have h_subset : closure (A ∩ B) ⊆ closure A := by
      apply closure_mono
      exact Set.inter_subset_left
    exact (interior_mono h_subset) hx
  have hxB : x ∈ interior (closure B) := by
    have h_subset : closure (A ∩ B) ⊆ closure B := by
      apply closure_mono
      exact Set.inter_subset_right
    exact (interior_mono h_subset) hx
  exact And.intro hxA hxB

theorem Topology.P1_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hP : ∀ i, Topology.P1 (X := X) (A i)) :
    Topology.P1 (X := X) (⋃ i, A i) := by
  classical
  dsimp [Topology.P1] at hP ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxAi⟩
  have hx_cl : x ∈ closure (interior (A i)) := (hP i) hxAi
  have h_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    -- `interior (A i)` is open and contained in the union
    have h_open : IsOpen (interior (A i)) := isOpen_interior
    have h_sub : interior (A i) ⊆ ⋃ j, A j := by
      intro y hy
      have hyAi : y ∈ A i := interior_subset hy
      exact Set.mem_iUnion.2 ⟨i, hyAi⟩
    exact interior_maximal h_sub h_open
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_subset
  exact h_closure_subset hx_cl

theorem Topology.P3_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hP : ∀ i, Topology.P3 (X := X) (A i)) :
    Topology.P3 (X := X) (⋃ i, A i) := by
  classical
  dsimp [Topology.P3] at hP ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxAi⟩
  have hxIntAi : x ∈ interior (closure (A i)) := hP i hxAi
  have hAi_subset : A i ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_closure_subset : closure (A i) ⊆ closure (⋃ j, A j) :=
    closure_mono hAi_subset
  have h_int_subset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure_subset
  exact h_int_subset hxIntAi

theorem Topology.P2_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hP : ∀ i, Topology.P2 (X := X) (A i)) :
    Topology.P2 (X := X) (⋃ i, A i) := by
  classical
  dsimp [Topology.P2] at hP ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxAi⟩
  have hxInt : x ∈ interior (closure (interior (A i))) := hP i hxAi
  -- Step 1:  interior (A i) ⊆ interior (⋃ j, A j)
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    have h_sub : interior (A i) ⊆ ⋃ j, A j := by
      intro y hy
      have hyAi : y ∈ A i := interior_subset hy
      exact Set.mem_iUnion.2 ⟨i, hyAi⟩
    exact interior_maximal h_sub isOpen_interior
  -- Step 2:  closure (interior (A i)) ⊆ closure (interior (⋃ j, A j))
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int_subset
  -- Step 3:  interior (closure (interior (A i))) ⊆ interior (closure (interior (⋃ j, A j)))
  have h_int_subset' :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) :=
    interior_mono h_closure_subset
  exact h_int_subset' hxInt

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hxA
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_dense] using hx_univ

theorem Topology.closed_P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hP2A : Topology.P2 (X := X) A) (hP2B : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∩ B) := by
  -- From `hAclosed` and `hP2A`, `A` is open.
  have hOpenA : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hAclosed hP2A
  -- From `hBclosed` and `hP2B`, `B` is open.
  have hOpenB : IsOpen B :=
    Topology.closed_P2_isOpen (X := X) (A := B) hBclosed hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A ∩ B) hOpenInter

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x hxA
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_dense, interior_univ] using hx_univ

theorem Topology.P3_closure_iff_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.closed_P3_iff_isOpen (X := X) (A := closure A) hClosed)

theorem Topology.isOpen_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  have hP1_of_open : Topology.P1 (X := X) A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hOpen
  have hP3_of_open : Topology.P3 (X := X) A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hOpen
  constructor
  · intro _; exact hP3_of_open
  · intro _; exact hP1_of_open

theorem Topology.isOpen_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  have h₁ : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P1_iff_P3 (X := X) (A := A) hOpen
  have h₂ : Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P2_iff_P3 (X := X) (A := A) hOpen
  exact h₁.trans h₂.symm

theorem Topology.interior_inter_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior (A ∪ B) := by
  -- `interior` is monotone with respect to set inclusion.
  refine interior_mono ?_
  intro x hx
  exact Or.inl hx.1

theorem Topology.interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- First, note that `interior A ⊆ A`.
  have h₁ : interior A ⊆ A := interior_subset
  -- Taking closures preserves this inclusion.
  have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono h₂

theorem Topology.closure_interior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) : closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem Topology.P2_closure_iff_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.closed_P2_iff_isOpen (X := X) (A := closure A) hClosed)

theorem Topology.interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  calc
    interior (closure A) = interior (Set.univ : Set X) := by
      simpa [h_dense]
    _ = (Set.univ : Set X) := by
      simpa [interior_univ]

theorem Topology.interior_closure_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hClosed : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hClosed.closure_eq]

theorem Topology.interior_closure_interior_eq_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    interior (closure (interior A)) = interior (closure A) := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact
    Topology.interior_closure_interior_eq_interior_closure_of_P1
      (X := X) (A := A) hP1

theorem Topology.isOpen_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  exact
    ⟨Topology.isOpen_implies_P1 (X := X) (A := A) hOpen,
      Topology.isOpen_implies_P2 (X := X) (A := A) hOpen,
      Topology.isOpen_implies_P3 (X := X) (A := A) hOpen⟩

theorem Topology.P2_closure_interior_iff_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.closed_P2_iff_isOpen (X := X) (A := closure (interior A)) hClosed)

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (⋃₀ 𝒜) := by
  classical
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hxUnion
  rcases Set.mem_sUnion.1 hxUnion with ⟨A, hA_mem, hxA⟩
  have hx_cl : x ∈ closure (interior A) := (h𝒜 A hA_mem) hxA
  have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
    have h_subset : A ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact interior_mono h_subset
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_cl

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P3 (X := X) A) :
    Topology.P3 (X := X) (⋃₀ 𝒜) := by
  classical
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hxUnion
  rcases Set.mem_sUnion.1 hxUnion with ⟨A, hA_mem, hxA⟩
  have hxInt : x ∈ interior (closure A) := h𝒜 A hA_mem hxA
  have h_closure_subset : closure A ⊆ closure (⋃₀ 𝒜) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_int_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono h_closure_subset
  exact h_int_subset hxInt

theorem Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  -- First simplify the innermost pattern using the existing lemma.
  have h₁ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := closure (interior A)))
  -- Next, collapse the remaining expression once more.
  have h₂ :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := A))
  -- Combine the two equalities to obtain the desired result.
  simpa [h₂] using h₁

theorem Topology.closed_P3_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 (X := X) A) :
    interior A = A := by
  have hOpen : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  simpa using hOpen.interior_eq

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ interior (closure A) := by
  exact interior_mono subset_closure

theorem Topology.interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (interior A).Nonempty := by
  classical
  -- Choose a point `x ∈ A`.
  rcases hA with ⟨x, hxA⟩
  -- By `P1`, this point lies in the closure of `interior A`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Either `interior A` is nonempty or it is empty; handle the two cases.
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  · -- If `interior A = ∅`, then its closure is also `∅`, contradicting `hx_cl`.
    have h_int_empty : interior A = (∅ : Set X) := by
      -- `interior A` has no elements, hence equals `∅`.
      by_contra hNe
      have : (interior A).Nonempty := (Set.nonempty_iff_ne_empty).2 hNe
      exact (hInt this)
    -- From this, the closure is also empty.
    have h_cl_empty : closure (interior A) = (∅ : Set X) := by
      simpa [h_int_empty, closure_empty]
    -- Derive the contradiction.
    have : x ∈ (∅ : Set X) := by
      simpa [h_cl_empty] using hx_cl
    exact this.elim

theorem Topology.P3_closure_interior_iff_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.closed_P3_iff_isOpen (X := X) (A := closure (interior A)) hClosed)

theorem Topology.interior_closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- `interior` is monotone, so the inclusion `A ⊆ B` gives
  -- `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono hAB
  -- Applying `closure` preserves inclusions.
  have hCl : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  -- Finally, use monotonicity of `interior` once more.
  exact interior_mono hCl

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) ↔ Topology.P3 (X := X) (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.closed_P2_iff_P3 (X := X) (A := closure A) hClosed)

theorem Topology.interior_closure_interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- First, simplify the innermost pattern using the existing lemma with
  -- `A := closure (interior A)`.
  have h₁ :
      interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
        (X := X) (A := closure (interior A)))
  -- Next, collapse the remaining expression once more with `A := A`.
  have h₂ :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
        (X := X) (A := A))
  -- Combine the two equalities to obtain the desired result.
  simpa [h₂] using h₁

theorem Topology.closed_P2_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) : interior A = A := by
  have hOpen : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hClosed hP2
  simpa using hOpen.interior_eq

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  -- We have the obvious inclusion `A ⊆ closure A`.
  have h_subset : A ⊆ closure A := subset_closure
  -- Apply the monotonicity of the `closure ∘ interior` operator.
  simpa using
    (Topology.closure_interior_mono (X := X) (A := A) (B := closure A) h_subset)

theorem Topology.interior_closure_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem Topology.P1_emptyInterior_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A)
    (hIntEmpty : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxA
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty] using hx_cl
  exact this

theorem Topology.closed_P3_closure_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} (hClosed : IsClosed A)
    (hP3 : Topology.P3 (X := X) A) : closure (interior A) = A := by
  -- From `hClosed` and `hP3`, the set `A` is open.
  have hOpen : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  -- Hence `interior A = A`.
  have hInt : interior A = A := hOpen.interior_eq
  -- Now take closures of both sides and use `hClosed`.
  calc
    closure (interior A) = closure A := by
      simpa [hInt]
    _ = A := by
      simpa [hClosed.closure_eq]

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P2 (X := X) A) :
    Topology.P2 (X := X) (⋃₀ 𝒜) := by
  classical
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hxUnion
  rcases Set.mem_sUnion.1 hxUnion with ⟨A, hA_mem, hxA⟩
  -- Use `P2` for the particular set `A`.
  have hxInt : x ∈ interior (closure (interior A)) := h𝒜 A hA_mem hxA
  -- `interior A` is contained in the interior of the union.
  have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
    have h_sub : A ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact interior_mono h_sub
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  -- Apply `interior_mono` once more.
  have h_int_subset' :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono h_closure_subset
  exact h_int_subset' hxInt

theorem Topology.closure_interior_eq_self_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hOpen : IsOpen A) :
    closure (interior A) = A := by
  simpa [hOpen.interior_eq, hClosed.closure_eq]

theorem Topology.P3_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, ?_, interior_subset⟩
    intro x hxA
    exact hP3 hxA
  · rintro ⟨U, hU_open, hA_U, hU_closure⟩
    dsimp [Topology.P3]
    intro x hxA
    have hxU : x ∈ U := hA_U hxA
    have hU_int : U ⊆ interior (closure A) :=
      interior_maximal hU_closure hU_open
    exact hU_int hxU

theorem Topology.P3_union_left_dense {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- First show that `A ∪ B` is dense in `X`.
  have h_dense_union : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    apply subset_antisymm
    · intro x _
      simp
    · intro x _
      -- Since `closure A = univ`, we have `x ∈ closure A`.
      have hxA : x ∈ closure A := by
        simpa [h_dense] using (by simp : (x : X) ∈ (Set.univ : Set X))
      -- And `closure A ⊆ closure (A ∪ B)` because `A ⊆ A ∪ B`.
      have h_sub : closure A ⊆ closure (A ∪ B) := closure_mono (by
        intro y hy
        exact Or.inl hy)
      exact h_sub hxA
  -- Conclude using `P3_of_dense`.
  exact Topology.P3_of_dense (X := X) (A := A ∪ B) h_dense_union

theorem Topology.isOpen_inter_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (X := X) (A ∩ B) ∧
    Topology.P2 (X := X) (A ∩ B) ∧
    Topology.P3 (X := X) (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A ∩ B) hOpen

theorem Topology.interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply subset_antisymm
  · -- `interior (closure (interior (closure A))) ⊆ interior (closure A)`
    have h₁ : closure (interior (closure A)) ⊆ closure A := by
      have h_inner : interior (closure A) ⊆ closure A := interior_subset
      have : closure (interior (closure A)) ⊆ closure (closure A) :=
        closure_mono h_inner
      simpa [closure_closure] using this
    exact interior_mono h₁
  · -- `interior (closure A) ⊆ interior (closure (interior (closure A)))`
    have h₂ : interior (closure A) ⊆ closure (interior (closure A)) := by
      intro x hx
      exact subset_closure hx
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    exact interior_maximal h₂ h_open

theorem Topology.P2_closure_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) → Topology.P3 (X := X) A := by
  intro hP2 x hxA
  -- First, regard `x` as a point of `closure A`.
  have hxCl : x ∈ closure A := subset_closure hxA
  -- Apply `P2` for `closure A`, landing `x` in `interior (closure (interior (closure A)))`.
  have hxInt₁ : x ∈ interior (closure (interior (closure A))) := hP2 hxCl
  -- Use the equality
  --   `interior (closure (interior (closure A))) = interior (closure A)`
  -- to rewrite the membership.
  have hxInt₂ : x ∈ interior (closure A) := by
    simpa [Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)] using hxInt₁
  -- Conclude the desired statement of `P3`.
  exact hxInt₂

theorem Topology.interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (X := X) A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩

theorem Topology.interior_closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  exact ⟨x, hxInt⟩

theorem Topology.P3_union_right_dense {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h_dense : closure B = (Set.univ : Set X)) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Use commutativity of `∪` to apply the existing `P3_union_left_dense`.
  have h : Topology.P3 (X := X) (B ∪ A) :=
    Topology.P3_union_left_dense (X := X) (A := B) (B := A) h_dense
  simpa [Set.union_comm] using h

theorem Topology.interior_closure_interior_inter_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have h_left : x ∈ interior (closure (interior A)) := by
    -- `interior (A ∩ B) ⊆ interior A`
    have h₁ : interior (A ∩ B) ⊆ interior A :=
      interior_mono Set.inter_subset_left
    -- Taking closures preserves inclusions
    have h₂ : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
      closure_mono h₁
    -- Apply `interior_mono` to obtain the desired inclusion
    exact (interior_mono h₂) hx
  have h_right : x ∈ interior (closure (interior B)) := by
    -- `interior (A ∩ B) ⊆ interior B`
    have h₁ : interior (A ∩ B) ⊆ interior B :=
      interior_mono Set.inter_subset_right
    -- Taking closures preserves inclusions
    have h₂ : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
      closure_mono h₁
    -- Apply `interior_mono` to obtain the desired inclusion
    exact (interior_mono h₂) hx
  exact And.intro h_left h_right

theorem Topology.closed_P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) :
    Topology.P1 (X := X) A := by
  -- From `hClosed` and `hP2`, we know `A` is open.
  have hOpen : IsOpen A := Topology.closed_P2_isOpen (X := X) (A := A) hClosed hP2
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem Topology.closed_compl_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P1 (X := X) (Aᶜ) ∧
      Topology.P2 (X := X) (Aᶜ) ∧
      Topology.P3 (X := X) (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hClosed
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := Aᶜ) hOpen

theorem Topology.P2_iff_exists_open_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A ↔
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  classical
  constructor
  · intro hP2
    refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
    · exact hP2
    · exact subset_rfl
  · rintro ⟨U, _, hAU, hUsubset⟩
    dsimp [Topology.P2]
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    exact hUsubset hxU

theorem Topology.closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem Topology.P1_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P1 (X := X) (A := interior (closure (interior A))) hOpen

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  -- First, `x` lies in `closure (interior A)`.
  have hx₁ : x ∈ closure (interior A) :=
    interior_subset hx
  -- Monotonicity of `closure` turns `interior A ⊆ A` into
  -- `closure (interior A) ⊆ closure A`, so `x ∈ closure A`.
  have hx₂ : x ∈ closure A :=
    (closure_mono (interior_subset : interior A ⊆ A)) hx₁
  exact hx₂

theorem Topology.P2_emptyInterior_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (X := X) A)
    (hIntEmpty : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  -- We prove that `A` contains no points.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxA
  -- `P2` puts points of `A` inside `interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- But the hypothesis tells us this interior is empty.
  have hInt_eq : interior (closure (interior A)) = (∅ : Set X) := by
    simp [hIntEmpty]
  -- Hence `x` lies in the empty set, contradiction.
  have : x ∈ (∅ : Set X) := by
    simpa [hInt_eq] using hxInt
  exact this.elim

theorem Topology.P2_union_left_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- First, show that `interior (A ∪ B)` is dense in `X`.
  have h_dense_union : closure (interior (A ∪ B)) = (Set.univ : Set X) := by
    -- `closure (interior (A ∪ B)) ⊆ univ` is immediate.
    have h₁ : closure (interior (A ∪ B)) ⊆ (Set.univ : Set X) := by
      intro x _
      simp
    -- For the reverse inclusion, use the density of `interior A`.
    have h₂ : (Set.univ : Set X) ⊆ closure (interior (A ∪ B)) := by
      have h_cl_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have h_int_subset : interior A ⊆ interior (A ∪ B) := by
          have hA_subset : A ⊆ A ∪ B := by
            intro x hx
            exact Or.inl hx
          exact interior_mono hA_subset
        exact h_int_subset
      simpa [h_dense] using h_cl_subset
    exact subset_antisymm h₁ h₂
  -- Apply the lemma that `P2` holds for sets with dense interior.
  exact Topology.P2_of_dense_interior (X := X) (A := A ∪ B) h_dense_union

theorem Topology.P3_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior (closure (interior A))) hOpen

theorem Topology.P3_emptyInteriorClosure_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (X := X) A)
    (hIntEmpty : interior (closure A) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxA
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEmpty] using hxInt
  exact this

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 (X := X) A := by
  -- First, show that `A` itself is dense, i.e. `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) := by
    -- `interior A ⊆ A`, so `closure (interior A) ⊆ closure A`.
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- Hence every point of `univ` lies in `closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      -- From `h_dense`, `x ∈ closure (interior A)`.
      have hx : x ∈ closure (interior A) := by
        simpa [h_dense] using (by
          have : (x : X) ∈ (Set.univ : Set X) := by
            simp
          exact this)
      exact h_subset hx
    -- The reverse inclusion is trivial.
    have h_closure_subset : closure A ⊆ (Set.univ : Set X) := by
      intro x _
      simp
    exact subset_antisymm h_closure_subset h_univ_subset
  -- Apply the existing lemma for dense sets.
  exact Topology.P3_of_dense (X := X) (A := A) h_closure_univ

theorem Topology.P1_closure_iff_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure A) ↔
      closure (interior (closure A)) = closure A := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.closed_P1_iff_closure_interior_eq_self
      (X := X) (A := closure A) hClosed)

theorem Topology.iUnion_interior_subset_interior_iUnion
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  classical
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  have h_subset : A i ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) :=
    interior_mono h_subset
  exact h_int_subset hxInt

theorem Topology.isOpen_closure_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) : Topology.P1 (X := X) (closure A) := by
  dsimp [Topology.P1]
  intro x hx_cl
  -- First, `A` is an open subset of `closure A`, hence contained in its interior.
  have h_subset : A ⊆ interior (closure A) :=
    interior_maximal subset_closure hOpen
  -- Taking closures preserves inclusions.
  have h_closure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono h_subset
  exact h_closure_subset hx_cl

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  -- Use the previously proven equality of the two closures
  have h_eq :=
    Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
      (X := X) (A := A)
  -- Rewrite `hx` using this equality to obtain the required membership
  simpa [h_eq] using (hx : x ∈ closure (interior (closure A)))

theorem Topology.interior_closure_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure A)) ∧
      Topology.P2 (X := X) (interior (closure A)) ∧
      Topology.P3 (X := X) (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := interior (closure A)) hOpen

theorem Topology.interior_union_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `A ⊆ A ∪ B`, hence `interior A ⊆ interior (A ∪ B)`
      have h_subset : interior A ⊆ interior (A ∪ B) := by
        have hA_sub : A ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono hA_sub
      exact h_subset hxA
  | inr hxB =>
      -- `B ⊆ A ∪ B`, hence `interior B ⊆ interior (A ∪ B)`
      have h_subset : interior B ⊆ interior (A ∪ B) := by
        have hB_sub : B ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono hB_sub
      exact h_subset hxB

theorem Topology.closure_interior_closure_interior_closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, simplify the innermost pattern using the existing 3-level idempotence lemma
  -- with `A := closure (interior A)`.
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := closure (interior A)))
  -- Next, collapse the remaining expression once more using the 2-level lemma.
  have h₂ :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := A))
  -- Combine the two equalities to obtain the desired result.
  simpa [h₂] using h₁

theorem Topology.closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X := X) A) :
    closure A = closure (interior (closure A)) := by
  apply subset_antisymm
  · -- `closure A ⊆ closure (interior (closure A))` via monotonicity of `closure`
    have h : A ⊆ interior (closure A) := hP3
    exact closure_mono h
  · -- `closure (interior (closure A)) ⊆ closure A`
    have h₁ : interior (closure A) ⊆ closure A := interior_subset
    have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono h₁
    simpa [closure_closure] using h₂

theorem Topology.interior_closure_eq_self_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hOpen : IsOpen A) :
    interior (closure A) = A := by
  have h₁ : interior (closure A) = interior A := by
    simpa using
      Topology.interior_closure_eq_interior_of_closed (X := X) (A := A) hClosed
  have h₂ : interior A = A := hOpen.interior_eq
  simpa [h₁, h₂]

theorem Topology.closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  -- From `interior A ⊆ A` we get `closure (interior A) ⊆ closure A`.
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Rewrite the density hypothesis to obtain `univ ⊆ closure A`.
  have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
    intro x _
    have hx : x ∈ closure (interior A) := by
      simpa [h_dense] using (by simp : (x : X) ∈ (Set.univ : Set X))
    exact h_subset hx
  -- Combine the two inclusions.
  apply subset_antisymm
  · intro _ _; simp
  · exact h_univ_subset

theorem Topology.P1_union_left_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (X := X) (A ∪ B) := by
  dsimp [Topology.P1]
  intro x hxUnion
  -- Every point of `X` lies in `closure (interior A)` by the density hypothesis.
  have hxClosureIntA : x ∈ closure (interior A) := by
    have : (x : X) ∈ (Set.univ : Set X) := by simp
    simpa [h_dense] using this
  -- Monotonicity of `closure ∘ interior` gives the required inclusion.
  have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
    apply closure_mono
    have h_int_subset : interior A ⊆ interior (A ∪ B) := by
      have h_sub : A ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact interior_mono h_sub
    exact h_int_subset
  exact h_subset hxClosureIntA

theorem Topology.interior_closure_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure (X := X) (A := A)
  exact ⟨x, h_subset hxInt₁⟩

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hxIntA
  -- First, upgrade the point from `interior A` to `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hxIntA
  -- Any element of a set lies in the closure of that set.
  exact subset_closure hxIntCl

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, use monotonicity of `closure`.
  have h₁ : closure A ⊆ closure B := closure_mono hAB
  -- Next, apply monotonicity of `interior`.
  have h₂ : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Finally, apply `closure` once more.
  exact closure_mono h₂

theorem Topology.closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    closure A ⊆ closure (interior A) := by
  -- From `P1` we know `A ⊆ closure (interior A)`.
  have h : (A : Set X) ⊆ closure (interior A) := hP1
  -- Taking closures preserves inclusions; simplify with `closure_closure`.
  simpa [closure_closure] using (closure_mono h)

theorem Topology.interior_iUnion_interior_eq_iUnion_interior
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (⋃ i, interior (A i) : Set X) = ⋃ i, interior (A i) := by
  classical
  -- The union of the open sets `interior (A i)` is open.
  have hOpen : IsOpen (⋃ i, interior (A i) : Set X) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  -- For an open set `U`, we have `interior U = U`.
  simpa [hOpen.interior_eq]

theorem Topology.not_P1_of_nonempty_emptyInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : A.Nonempty) (hIntEmpty : interior A = (∅ : Set X)) :
    ¬ Topology.P1 (X := X) A := by
  intro hP1
  -- From `P1` and `hA`, the interior of `A` must be nonempty.
  have hIntNon : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA
  -- But this contradicts the hypothesis that the interior is empty.
  simpa [hIntEmpty] using hIntNon

theorem Topology.P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P2 (X := X) (closure A) := by
  exact (Topology.P2_closure_iff_open_closure (X := X) (A := A)).2 hOpen

theorem Topology.not_P2_of_nonempty_emptyInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : A.Nonempty) (hIntEmpty : interior (closure (interior A)) = (∅ : Set X)) :
    ¬ Topology.P2 (X := X) A := by
  intro hP2
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEmpty] using hxInt
  exact this.elim

theorem Topology.closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- `interior (closure A)` is clearly contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves this inclusion.
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h₂

theorem Topology.P2_union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hP2A : Topology.P2 (X := X) A) (hOpenU : IsOpen U) :
    Topology.P2 (X := X) (A ∪ U) := by
  -- Any open set satisfies `P2`.
  have hP2U : Topology.P2 (X := X) U :=
    Topology.isOpen_implies_P2 (X := X) (A := U) hOpenU
  -- Apply the union lemma for `P2`.
  exact Topology.P2_union (X := X) (A := A) (B := U) hP2A hP2U

theorem Topology.isOpen_P1_iff_P2_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ↔
      (Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A) := by
  -- We already know `P1 ↔ P2` and `P1 ↔ P3` for open sets.
  have hP1P2 : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.isOpen_P1_iff_P2 (X := X) (A := A) hOpen
  have hP1P3 : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P1_iff_P3 (X := X) (A := A) hOpen
  constructor
  · intro hP1
    have hP2 : Topology.P2 (X := X) A := (hP1P2).1 hP1
    have hP3 : Topology.P3 (X := X) A := (hP1P3).1 hP1
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    exact (hP1P2).2 hP2

theorem Topology.interior_closure_interior_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    interior (closure (interior A)) = (Set.univ : Set X) := by
  simpa [h_dense, interior_univ]

theorem Topology.interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact (subset_closure : interior (closure A) ⊆ closure (interior (closure A))) hx

theorem Topology.interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A :=
    (interior_mono Set.inter_subset_left) hx
  have hxB : x ∈ interior B :=
    (interior_mono Set.inter_subset_right) hx
  exact And.intro hxA hxB

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A → Topology.P1 (X := X) (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxClA
  -- Step 1:  `closure A ⊆ closure (interior A)` by the given `P1`.
  have h₁ : closure A ⊆ closure (interior A) :=
    Topology.closure_subset_closure_interior_of_P1 (X := X) (A := A) hP1
  -- Hence `x ∈ closure (interior A)`.
  have hxClIntA : x ∈ closure (interior A) := h₁ hxClA
  -- Step 2:  `closure (interior A) ⊆ closure (interior (closure A))`
  --          by monotonicity of `interior` and `closure`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    exact Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Combine the two inclusions to obtain the goal.
  exact h₂ hxClIntA

theorem Topology.inter_interior_subset_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ interior B ⊆ interior (A ∩ B) := by
  intro x hx
  have hOpen : IsOpen (interior A ∩ interior B) :=
    (isOpen_interior.inter isOpen_interior)
  have h_subset : interior A ∩ interior B ⊆ A ∩ B := by
    intro y hy
    exact And.intro (interior_subset hy.1) (interior_subset hy.2)
  have h : interior A ∩ interior B ⊆ interior (A ∩ B) :=
    interior_maximal h_subset hOpen
  exact h hx

theorem Topology.P3_union_left_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- From the density of `interior A`, deduce that `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (X := X) (A := A) h_dense
  -- Apply the existing lemma for sets whose closure is the whole space.
  exact
    Topology.P3_union_left_dense (X := X) (A := A) (B := B) h_closure_univ

theorem Topology.closure_interior_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  simp [interior_interior]

theorem Topology.closure_interior_closure_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure A))) = closure (interior (closure A)) := by
  simp [closure_closure]

theorem Topology.interior_iInter_subset_iInter_interior
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (⋂ i, A i : Set X) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- For each index `i`, `(⋂ i, A i) ⊆ A i`.
  have hxi : ∀ i, x ∈ interior (A i) := by
    intro i
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    exact (interior_mono h_subset) hx
  exact Set.mem_iInter.2 hxi

theorem Topology.P2_union_right_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior B) = (Set.univ : Set X)) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- Apply the existing left-dense lemma after swapping `A` and `B`.
  have h : Topology.P2 (X := X) (B ∪ A) :=
    Topology.P2_union_left_denseInterior (X := X) (A := B) (B := A) h_dense
  simpa [Set.union_comm] using h

theorem Topology.interior_inter_eq_inter_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B : Set X) = interior A ∩ interior B := by
  apply subset_antisymm
  · exact
      Topology.interior_inter_subset_inter_interior (X := X) (A := A) (B := B)
  · exact
      Topology.inter_interior_subset_interior_inter (X := X) (A := A) (B := B)

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A → Topology.P1 (X := X) (closure A) := by
  intro hP3
  dsimp [Topology.P1, Topology.P3] at hP3 ⊢
  intro x hxClA
  -- From `P3`, we have `A ⊆ interior (closure A)`.
  have h_subset : (closure A : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono hP3
  exact h_subset hxClA

theorem Topology.clopen_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A) hOpen

theorem Topology.P1_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior (closure (interior A)))) := by
  -- First, rewrite the set using the idempotence lemma.
  have h_eq :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior (X := X) (A := A)
  -- We already know that `closure (interior A)` satisfies `P1`.
  have hP1 : Topology.P1 (X := X) (closure (interior A)) :=
    Topology.P1_closure_interior (X := X) (A := A)
  -- Transport `P1` along the established equality.
  simpa [h_eq] using hP1

theorem Topology.denseInterior_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A ∧
      Topology.P2 (X := X) A ∧
      Topology.P3 (X := X) A := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_dense_interior (X := X) (A := A) h_dense
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h_dense
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P3_of_dense_interior (X := X) (A := A) h_dense
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.isOpen_closure_iff_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure A) ↔ interior (closure A) = closure A := by
  constructor
  · intro hOpen
    exact hOpen.interior_eq
  · intro h_eq
    have hOpenInt : IsOpen (interior (closure A)) := isOpen_interior
    simpa [h_eq] using hOpenInt

theorem Topology.isOpen_P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P2 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) := by
  -- Equivalences between `P1`, `P2`, and `P3` for open sets.
  have hP1P2 : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.isOpen_P1_iff_P2 (X := X) (A := A) hOpen
  have hP1P3 : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P1_iff_P3 (X := X) (A := A) hOpen
  constructor
  · intro hP2
    -- Obtain `P1` from `P2`.
    have hP1 : Topology.P1 (X := X) A := (hP1P2).2 hP2
    -- Obtain `P3` from `P1`.
    have hP3 : Topology.P3 (X := X) A := (hP1P3).1 hP1
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    -- Obtain `P2` from `P1`.
    exact (hP1P2).1 hP1

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) (closure A) := by
  intro hP2
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact Topology.P3_implies_P1_closure (X := X) (A := A) hP3

theorem Topology.P2_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) → Topology.P1 (X := X) (closure A) := by
  intro hP2
  have hClosed : IsClosed (closure A) := isClosed_closure
  exact Topology.closed_P2_implies_P1 (X := X) (A := closure A) hClosed hP2

theorem Topology.P1_union_right_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior B) = (Set.univ : Set X)) :
    Topology.P1 (X := X) (A ∪ B) := by
  have h : Topology.P1 (X := X) (B ∪ A) :=
    Topology.P1_union_left_denseInterior (X := X) (A := B) (B := A) h_dense
  simpa [Set.union_comm] using h

theorem Topology.closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- Since `interior A ⊆ closure (interior A)`, the right-hand side being empty
    -- forces `interior A` itself to be empty.
    have hsubset : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure (interior A) := subset_closure hx
      simpa [h] using this
    have hIntEmpty : interior A = (∅ : Set X) := by
      apply Set.eq_of_subset_of_subset hsubset
      intro x hx
      cases hx
    exact hIntEmpty
  · intro h
    -- If `interior A` is empty, its closure is also empty.
    simpa [h, closure_empty]

theorem Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
      simpa using
        (Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
          (X := X) (A := closure A))
    _ = interior (closure A) := by
      simpa using
        (Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A))

theorem Topology.P3_closure_implies_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) → Topology.P2 (X := X) (closure A) := by
  intro hP3
  exact (Topology.P2_closure_iff_P3_closure (X := X) (A := A)).mpr hP3

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          have h :=
            Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
              (X := X) (A := A)
          simpa [h]
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq_interior_closure
              (X := X) (A := A))

theorem Topology.closure_interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP1 hxA⟩

theorem Topology.interior_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior (closure A)) = interior (closure A) := by
  simpa [interior_interior]

theorem Topology.isOpen_P3_iff_P1_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P3 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A) := by
  -- Existing equivalences for open sets.
  have hP1P3 : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P1_iff_P3 (X := X) (A := A) hOpen
  have hP1P2 : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.isOpen_P1_iff_P2 (X := X) (A := A) hOpen
  -- Build the desired equivalence.
  constructor
  · intro hP3
    -- Obtain `P1` from `P3`, and then `P2` from `P1`.
    have hP1 : Topology.P1 (X := X) A := (hP1P3).mpr hP3
    have hP2 : Topology.P2 (X := X) A := (hP1P2).1 hP1
    exact And.intro hP1 hP2
  · rintro ⟨hP1, _⟩
    -- From `P1`, deduce `P3`.
    exact (hP1P3).1 hP1

theorem Topology.P1_iff_closure_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)`, take closures of both sides.
    have : closure A ⊆ closure (closure (interior A)) :=
      closure_mono (hP1 : A ⊆ closure (interior A))
    simpa [closure_closure] using this
  · intro hClSub
    -- Use the inclusion on closures to obtain the original `P1`.
    dsimp [Topology.P1]
    intro x hxA
    have hxCl : (x : X) ∈ closure A := subset_closure hxA
    exact hClSub hxCl

theorem Topology.closure_interior_eq_univ_of_dense_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X))
    (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = (Set.univ : Set X) := by
  -- From `P1`, we know `closure (interior A) = closure A`.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  -- Combine this with the density hypothesis `closure A = univ`.
  simpa [h_dense] using h_eq

theorem Topology.closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hxCl : x ∈ closure (interior A) := interior_subset hxInt
  exact ⟨x, hxCl⟩

theorem Topology.interior_closure_union_eq_interior_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]

theorem Topology.closure_interior_union_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
  -- The union of two open sets is open.
  have hUnionOpen : IsOpen (A ∪ B) := hA.union hB
  -- For an open set, its interior is itself.
  have hIntEq : interior (A ∪ B) = A ∪ B := hUnionOpen.interior_eq
  -- Rewrite and use the standard formula for the closure of a union.
  simpa [hIntEq, closure_union]

theorem Topology.interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior A).Nonempty := by
  classical
  -- Pick a point `x ∈ A`.
  rcases hA with ⟨x, hxA⟩
  -- `P2` sends this point inside `interior (closure (interior A))`.
  have hxIntCl : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Either `interior A` is nonempty or it is empty.
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  · -- If `interior A` is empty, derive a contradiction with `hxIntCl`.
    -- First, record this emptiness.
    have hIntEmpty : interior A = (∅ : Set X) := by
      apply (Set.eq_empty_iff_forall_not_mem).2
      intro y hy
      have : (interior A).Nonempty := ⟨y, hy⟩
      exact (hInt this).elim
    -- Then `interior (closure (interior A))` is also empty.
    have hIntClEmpty : interior (closure (interior A)) = (∅ : Set X) := by
      simp [hIntEmpty]
    -- But `x` was assumed to lie in this empty set—contradiction.
    have : x ∈ (∅ : Set X) := by
      simpa [hIntClEmpty] using hxIntCl
    cases this

theorem Topology.closure_interior_closure_interior_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (interior A)))) =
      closure (interior A) := by
  simpa [interior_interior] using
    (Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A))

theorem Topology.P3_closure_implies_P1_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) → Topology.P1 (X := X) (closure A) := by
  intro hP3
  have hClosed : IsClosed (closure A) := isClosed_closure
  exact Topology.closed_P3_implies_P1 (X := X) (A := closure A) hClosed hP3

theorem Topology.interior_closure_inter_closure_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B : Set X) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- First inclusion: `closure A ∩ closure B ⊆ closure A`.
  have hxA : x ∈ interior (closure A) := by
    have h_subset : (closure A ∩ closure B : Set X) ⊆ closure A := by
      intro y hy; exact hy.1
    exact (interior_mono h_subset) hx
  -- Second inclusion: `closure A ∩ closure B ⊆ closure B`.
  have hxB : x ∈ interior (closure B) := by
    have h_subset : (closure A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact (interior_mono h_subset) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- First, simplify the innermost pattern using the existing lemma with
  -- `A := interior (closure (interior A))`.
  have h₁ :
      interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := interior (closure (interior A))))
  -- Next, collapse the remaining expression once more with `A := interior A`.
  have h₂ :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := interior A))
  -- Combine the two equalities to obtain the desired result.
  simpa [h₂] using h₁

theorem Topology.interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A) ∪ closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  exact interior_mono
    (Topology.closure_interior_union_subset (X := X) (A := A) (B := B))

theorem Topology.interior_closure_iInter_subset_iInter_interior_closure
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (closure (⋂ i, A i : Set X)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- Show that `x` belongs to `interior (closure (A i))` for each `i`.
  have hx_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- Because `(⋂ i, A i) ⊆ A i`, we get the inclusion on closures.
    have h_subset : closure (⋂ j, A j : Set X) ⊆ closure (A i) := by
      apply closure_mono
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Use monotonicity of `interior` to transport `hx`.
    exact (interior_mono h_subset) hx
  -- Re-assemble the pointwise membership into an intersection.
  exact Set.mem_iInter.2 hx_i

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x _
  simpa [closure_univ, interior_univ]

theorem Topology.interior_iUnion_eq_iUnion {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hOpen : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  classical
  -- The union of open sets is open.
  have hUnionOpen : IsOpen (⋃ i, A i : Set X) := by
    apply isOpen_iUnion
    intro i
    exact hOpen i
  -- For an open set, its interior is itself.
  simpa [hUnionOpen.interior_eq]

theorem Topology.interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x _
  simp [closure_univ, interior_univ]

theorem Topology.interior_union_eq_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa using hOpen.interior_eq

theorem Topology.closed_P3_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P3 (X := X) A ↔ interior A = A := by
  -- First, use the existing equivalence between `P3` and openness for closed sets.
  have h₀ := Topology.closed_P3_iff_isOpen (X := X) (A := A) hClosed
  -- We now relate openness to the interior being equal to the set itself.
  constructor
  · -- `P3 A → interior A = A`
    intro hP3
    -- Convert `P3` into openness via `h₀`.
    have hOpen : IsOpen A := (h₀).1 hP3
    -- For an open set, `interior` is itself.
    simpa using hOpen.interior_eq
  · -- `interior A = A → P3 A`
    intro hInt
    -- From the equality, deduce that `A` is open.
    have hOpen : IsOpen A := by
      -- `interior A` is open, and it equals `A`.
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hInt] using hOpenInt
    -- Convert openness back to `P3` via the established equivalence.
    exact (h₀).2 hOpen

theorem Topology.interior_eq_self_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hInt : interior A = A) :
    Topology.P1 (X := X) A ∧
      Topology.P2 (X := X) A ∧
      Topology.P3 (X := X) A := by
  -- From `interior A = A`, deduce that `A` is open.
  have hOpen : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using this
  -- Any open set satisfies all three properties.
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A) hOpen

theorem Topology.P1_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A) :
    A ⊆ closure (interior (closure A)) := by
  intro x hxA
  -- From `P1`, the point `x` lies in `closure (interior A)`.
  have hxClInt : x ∈ closure (interior A) := hP1 hxA
  -- We have `interior A ⊆ interior (closure A)`.
  have hInt : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Taking closures preserves inclusions.
  have hCl : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono hInt
  -- Combine the facts to conclude.
  exact hCl hxClInt

theorem Topology.P3_union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hP3A : Topology.P3 (X := X) A) (hOpenU : IsOpen U) :
    Topology.P3 (X := X) (A ∪ U) := by
  -- An open set automatically satisfies `P3`.
  have hP3U : Topology.P3 (X := X) U :=
    Topology.isOpen_implies_P3 (X := X) (A := U) hOpenU
  -- Combine the two `P3` sets using the existing union lemma.
  exact Topology.P3_union (X := X) (A := A) (B := U) hP3A hP3U

theorem Topology.P3_closure_iff_interior_closure_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) ↔ interior (closure A) = closure A := by
  have h₁ := Topology.P3_closure_iff_open_closure (X := X) (A := A)
  have h₂ := Topology.isOpen_closure_iff_interior_eq_self (X := X) (A := A)
  exact h₁.trans h₂

theorem Topology.P2_emptyInteriorClosureInterior_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A)
    (hIntEmpty : interior (closure (interior A)) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEmpty] using hxInt
  exact this.elim

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem Topology.interior_inter_eq_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B : Set X) = A ∩ B := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- For an open set, its interior is itself.
  simpa using hOpen.interior_eq

theorem Topology.interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior (A : Set X)) = interior A := by
  simpa [interior_interior]

theorem Topology.closure_interior_diff_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- First, note that `A \ B ⊆ A`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `interior` transports this inclusion.
  have h_int_subset : interior (A \ B : Set X) ⊆ interior A :=
    interior_mono h_subset
  -- Finally, taking closures preserves inclusions.
  exact closure_mono h_int_subset

theorem Topology.closed_P2_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P2 (X := X) A ↔ interior A = A := by
  -- First, rewrite `P2` in terms of openness via the existing lemma.
  have h₁ : Topology.P2 (X := X) A ↔ IsOpen A :=
    Topology.closed_P2_iff_isOpen (X := X) (A := A) hClosed
  -- Next, relate openness to the equality `interior A = A`.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem Topology.open_closure_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) :
    Topology.P1 (X := X) (closure A) ∧
      Topology.P2 (X := X) (closure A) ∧
      Topology.P3 (X := X) A := by
  -- `P1` holds for `closure A` because it is open.
  have hP1 : Topology.P1 (X := X) (closure A) := by
    simpa [closure_closure] using
      (Topology.isOpen_closure_implies_P1 (X := X) (A := closure A) hOpen)
  -- `P2` holds for `closure A` by openness of `closure A`.
  have hP2 : Topology.P2 (X := X) (closure A) :=
    Topology.P2_of_open_closure (X := X) (A := A) hOpen
  -- `P3` holds for `A` when `closure A` is open.
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P3_of_open_closure (X := X) (A := A) hOpen
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.closure_interior_inter_interior_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B : Set X) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior A ∩ interior B ⊆ interior A`
  have hx_left : x ∈ closure (interior A) := by
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior A := by
      intro y hy; exact hy.1
    exact (closure_mono h_subset) hx
  -- `interior A ∩ interior B ⊆ interior B`
  have hx_right : x ∈ closure (interior B) := by
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior B := by
      intro y hy; exact hy.2
    exact (closure_mono h_subset) hx
  exact And.intro hx_left hx_right

theorem Topology.closure_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem Topology.closure_interior_closure_interior_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    closure (interior (closure (interior A))) = closure A := by
  have h₁ :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  have h₂ : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  simpa [h₂] using h₁

theorem Topology.closure_interior_union_eq_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure (A ∪ B) := by
  calc
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
      simpa using
        Topology.closure_interior_union_eq_closure_union
          (X := X) (A := A) (B := B) hA hB
    _ = closure (A ∪ B) := by
      simpa [closure_union] using
        (closure_union (A := A) (B := B)).symm

theorem Topology.P3_closure_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P3 (X := X) (closure A) := by
  exact (Topology.P3_closure_iff_open_closure (X := X) (A := A)).2 hOpen

theorem Topology.isOpen_iff_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A ↔ A ⊆ interior A := by
  constructor
  · intro hOpen
    -- For an open set, its interior is itself.
    have h_eq : interior A = A := hOpen.interior_eq
    -- Rewriting with this equality yields the inclusion.
    simpa [h_eq]
  · intro hSubset
    -- `interior A` is open, and the assumed inclusion together with `interior_subset`
    -- gives equality of the two sets.
    have h_eq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact hSubset
    -- Conclude that `A` is open by rewriting.
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))

theorem Topology.interior_closure_diff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure A) := by
  -- The set difference `A \ B` is contained in `A`.
  have h₁ : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions.
  have h₂ : closure (A \ B : Set X) ⊆ closure A :=
    closure_mono h₁
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono h₂

theorem Topology.closure_interior_iUnion_subset {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} :
    (⋃ i, closure (interior (A i)) : Set X) ⊆
      closure (interior (⋃ i, A i)) := by
  classical
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior (A i)` is contained in `interior (⋃ i, A i)`
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    have h_sub : (A i) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_sub
  -- Taking closures preserves the inclusion.
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_i

theorem Topology.closure_interior_inter_eq_closure_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) = closure (interior A ∩ interior B) := by
  simpa [Topology.interior_inter_eq_inter_interior (X := X) (A := A) (B := B)]

theorem Topology.iterate_closure_interior_fixed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    ∀ n : ℕ,
      ((fun S : Set X => closure (interior S))^[n]) (closure (interior A)) =
        closure (interior A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Function.iterate_succ_apply', ih,
        Topology.closure_interior_closure_interior_eq_closure_interior
          (X := X) (A := closure (interior A))]

theorem Topology.iterate_interior_closure_fixed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      ((fun S : Set X => interior (closure S))^[n]) (interior (closure A)) =
        interior (closure A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Function.iterate_succ_apply', ih,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A)]

theorem Topology.isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) : Topology.P1 (X := X) (closure A) := by
  -- First, any open set satisfies `P1`.
  have hP1A : Topology.P1 (X := X) A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hOpen
  -- Transport `P1` from `A` to its closure using the existing lemma.
  exact Topology.P1_closure_of_P1 (X := X) (A := A) hP1A

theorem Topology.closure_interior_closure_eq_closure_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hClosed : IsClosed A) :
    closure (interior (closure A)) = closure (interior A) := by
  simpa [hClosed.closure_eq]

theorem Topology.iterate_closure_interior_fixed_aux {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    ∀ n : ℕ,
      ((fun S : Set X => closure (interior S))^[n]) (closure (interior A)) =
        closure (interior A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- `closure (interior A)` is a fixed point of the operator `S ↦ closure (interior S)`
      have h_fix :
          closure (interior (closure (interior A))) = closure (interior A) := by
        simpa using
          Topology.closure_interior_closure_interior_eq_closure_interior
            (X := X) (A := A)
      -- Use the fixed-point property to simplify the `(n + 1)`-st iterate.
      simp [Function.iterate_succ_apply', ih, h_fix]

theorem Topology.interior_closure_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- `closure A ⊆ univ` is trivial.
    have h₁ : closure A ⊆ (Set.univ : Set X) := by
      intro _ _; simp
    -- Every point of `univ` lies in `closure A` because it lies in `interior (closure A)`.
    have h₂ : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      have hxInt : (x : X) ∈ interior (closure A) := by
        simpa [hInt] using (by simp : (x : X) ∈ (Set.univ : Set X))
      exact (interior_subset : interior (closure A) ⊆ closure A) hxInt
    exact Set.Subset.antisymm h₁ h₂
  · intro hCl
    exact
      Topology.interior_closure_eq_univ_of_dense
        (X := X) (A := A) hCl

theorem Topology.closure_interior_iInter_subset_iInter_closure_interior
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (interior (⋂ i, A i : Set X)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  have hxi : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- `interior` is monotone, so transport the basic inclusion
    have h_subset : interior (⋂ j, A j : Set X) ⊆ interior (A i) := by
      have h₀ : (⋂ j, A j : Set X) ⊆ A i :=
        Set.iInter_subset (fun j => A j) i
      exact interior_mono h₀
    -- Apply `closure_mono` to obtain the desired membership
    exact (closure_mono h_subset) hx
  exact Set.mem_iInter.2 hxi

theorem Topology.iUnion_interior_closure_subset_interior_closure_iUnion
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    (⋃ i, interior (closure (A i)) : Set X) ⊆
      interior (closure (⋃ i, A i)) := by
  classical
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `closure (A i)` is contained in `closure (⋃ j, A j)`.
  have h_closure_subset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Applying `interior_mono` yields the desired inclusion on interiors.
  have h_int_subset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure_subset
  exact h_int_subset hx_i

theorem Topology.closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]

theorem Topology.closure_interior_closure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (closure A)) :
    closure (interior (closure A)) = closure A := by
  simpa using
    (Topology.closure_interior_eq_closure_of_isOpen (X := X) (A := closure A) hOpen)

theorem Topology.interior_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  -- `A \ B` is contained in `A`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Apply monotonicity of `interior`.
  exact interior_mono h_subset

theorem Topology.iterate_interior_closure_fixed_aux
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      interior (closure ((fun S : Set X => interior (closure S))^[n] A)) =
        interior (closure A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Function.iterate_succ_apply', ih,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X)
          (A := ((fun S : Set X => interior (closure S))^[n] A))]

theorem Topology.isClosed_iff_closure_subset_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A ↔ closure A ⊆ A := by
  constructor
  · intro hClosed
    -- If `A` is closed, its closure is itself, hence the desired inclusion.
    have h_eq : closure A = A := hClosed.closure_eq
    have h_subset : (A : Set X) ⊆ A := subset_rfl
    simpa [h_eq] using (h_subset : (A : Set X) ⊆ A)
  · intro h_subset
    -- The inclusion `closure A ⊆ A` together with the opposite
    -- inclusion `A ⊆ closure A` yields equality, hence closedness.
    have h_eq : closure A = A := by
      apply subset_antisymm h_subset
      exact subset_closure
    -- Rewriting with this equality turns the known closedness of
    -- `closure A` into the closedness of `A`.
    have h_closed_closure : IsClosed (closure A) := isClosed_closure
    simpa [h_eq] using h_closed_closure

theorem Topology.closure_interior_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∪ B)) ⊆ closure A ∪ closure B := by
  intro x hx
  -- `interior (A ∪ B)` is contained in `A ∪ B`.
  have h_subset : (interior (A ∪ B) : Set X) ⊆ A ∪ B := interior_subset
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior (A ∪ B)) ⊆ closure (A ∪ B) :=
    closure_mono h_subset
  -- Transport the membership of `x`.
  have hx_closure : x ∈ closure (A ∪ B) := h_closure_subset hx
  -- Rewriting the right‐hand side using `closure_union`.
  simpa [closure_union] using hx_closure

theorem Topology.closure_unionInterior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B : Set X) ⊆
      closure (interior (A ∪ B)) := by
  -- `interior A ∪ interior B` is contained in `interior (A ∪ B)`
  have h_subset :
      (interior A ∪ interior B : Set X) ⊆ interior (A ∪ B) :=
    Topology.interior_union_subset_interior_union (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions
  exact closure_mono h_subset

theorem Topology.isClosed_of_closure_interior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = A) : IsClosed A := by
  -- `closure (interior A)` is always closed.
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  -- Rewrite using the provided equality.
  simpa [h] using hClosed

theorem Topology.open_subset_closure_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hUopen : IsOpen U) (hUsubset : U ⊆ closure A) :
    U ⊆ interior (closure A) := by
  exact interior_maximal hUsubset hUopen

theorem Topology.isClosed_iff_closure_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A ↔ closure A = A := by
  constructor
  · intro hClosed
    simpa using hClosed.closure_eq
  · intro hEq
    have hClosedCl : IsClosed (closure A) := isClosed_closure
    simpa [hEq] using hClosedCl

theorem Topology.interior_diff_subset_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ A \ closure B := by
  intro x hx
  -- A point in the interior of `A \ B` certainly lies in `A \ B`.
  have hx_diff : x ∈ A \ B := interior_subset hx
  have hxA : x ∈ A := hx_diff.1
  -- We show that such a point cannot be in `closure B`.
  have hx_not_clB : x ∉ closure B := by
    intro hx_clB
    -- `interior (A \ B)` is an open neighbourhood of `x` contained in the complement of `B`.
    have h_open : IsOpen (interior (A \ B : Set X)) := isOpen_interior
    -- If `x ∈ closure B`, every open neighbourhood of `x` meets `B`.
    have h_nonempty : ((interior (A \ B : Set X)) ∩ B).Nonempty :=
      (mem_closure_iff.1 hx_clB) (interior (A \ B : Set X)) h_open hx
    rcases h_nonempty with ⟨y, hyInt, hyB⟩
    -- But `interior (A \ B)` is contained in `A \ B`, hence disjoint from `B`.
    have : y ∈ A \ B := interior_subset hyInt
    exact (this.2) hyB
  exact And.intro hxA hx_not_clB

theorem Topology.closed_P2_interiorClosureInterior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) :
    interior (closure (interior A)) = A := by
  -- From closedness and `P2`, we already know two equalities.
  have h_cl : closure (interior A) = A :=
    Topology.closed_P2_closure_interior_eq_self (X := X) (A := A) hClosed hP2
  have h_int : interior A = A :=
    Topology.closed_P2_interior_eq_self (X := X) (A := A) hClosed hP2
  -- Rewrite twice to obtain the desired result.
  calc
    interior (closure (interior A)) = interior A := by
      simpa [h_cl]
    _ = A := by
      simpa [h_int]

theorem Topology.P2_closure_implies_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) → Topology.P3 (X := X) (closure A) := by
  intro hP2
  have hEquiv := (Topology.P2_closure_iff_P3_closure (X := X) (A := A))
  exact hEquiv.1 hP2

theorem Topology.interior_closure_interior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  -- From `P1` and the non‐emptiness of `A`, we know `interior A` is nonempty.
  have hIntA : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA
  -- The inclusion `interior A ⊆ interior (closure (interior A))`.
  have hSubset :
      interior A ⊆ interior (closure (interior A)) :=
    Topology.interior_subset_interior_closure_interior (X := X) (A := A)
  -- Transport the witness of non‐emptiness along this inclusion.
  rcases hIntA with ⟨x, hxIntA⟩
  exact ⟨x, hSubset hxIntA⟩

theorem Topology.P3_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (Set.univ : Set X)) :
    Topology.P3 (X := X) A := by
  -- First, turn the hypothesis into the density statement `closure A = univ`.
  have h_closure : closure A = (Set.univ : Set X) :=
    (Topology.interior_closure_eq_univ_iff (X := X) (A := A)).1 h
  -- Conclude using the existing lemma for dense sets.
  exact Topology.P3_of_dense (X := X) (A := A) h_closure

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  apply Set.Subset.antisymm
  · -- `⊆` direction
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : A ∩ B ⊆ A)) hx
    have hxAB : x ∈ (A ∩ B) := interior_subset hx
    exact And.intro hxA hxAB.2
  · -- `⊇` direction
    intro x hx
    rcases hx with ⟨hxIntA, hxB⟩
    -- The set `interior A ∩ B` is an open neighborhood of `x`
    have hOpen : IsOpen (interior A ∩ B) :=
      (isOpen_interior.inter hB)
    have hSubset : interior A ∩ B ⊆ A ∩ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    -- By the characterization of the interior, `x` belongs to `interior (A ∩ B)`
    exact interior_maximal hSubset hOpen (And.intro hxIntA hxB)

theorem Topology.closure_interior_union_eq_univ_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    closure (interior (A ∪ B)) = (Set.univ : Set X) := by
  apply subset_antisymm
  · intro x _
    simp
  · intro x _
    -- From the density hypothesis, `x ∈ closure (interior A)`.
    have hxA : (x : X) ∈ closure (interior A) := by
      simpa [h_dense] using (by simp : (x : X) ∈ (Set.univ : Set X))
    -- `interior A ⊆ interior (A ∪ B)` by monotonicity of `interior`.
    have h_int_subset : (interior A : Set X) ⊆ interior (A ∪ B) := by
      have hA_subset : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact interior_mono hA_subset
    -- Taking closures preserves inclusions.
    have h_cl_subset :
        closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono h_int_subset
    -- Conclude that `x ∈ closure (interior (A ∪ B))`.
    have : (x : X) ∈ closure (interior (A ∪ B)) := h_cl_subset hxA
    simpa using this

theorem Topology.isClosed_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior A)) := by
  simpa using (isClosed_closure : IsClosed (closure (interior A)))

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx

theorem Topology.interior_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior (closure (interior A))) = interior (closure (interior A)) := by
  simpa [interior_interior]

theorem Topology.isClosed_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior (closure A))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (closure A))))

theorem Topology.open_and_closed_of_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior A = closure A) :
    IsOpen A ∧ IsClosed A := by
  -- First, show that `A` is open.
  have hInt : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    ·
      have hSub : (A : Set X) ⊆ closure A := subset_closure
      simpa [h] using hSub
  have hOpen : IsOpen A := by
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using hOpenInt
  -- Next, show that `A` is closed.
  have hCl : closure A = A := by
    apply subset_antisymm
    ·
      intro x hx
      have hxInt : x ∈ interior A := by
        simpa [h] using hx
      exact interior_subset hxInt
    · exact subset_closure
  have hClosed : IsClosed A := by
    have : IsClosed (closure A) := isClosed_closure
    simpa [hCl] using this
  exact And.intro hOpen hClosed



theorem Topology.P1_iterate_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    ∀ n : ℕ,
      Topology.P1 (X := X)
        (((fun S : Set X => closure (interior S))^[n.succ]) A) := by
  intro n
  induction n with
  | zero =>
      simpa using
        (Topology.P1_closure_interior (X := X) (A := A))
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using
        (Topology.P1_closure_interior (X := X)
          (A := ((fun S : Set X => closure (interior S))^[n.succ] A)))

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hxB : x ∈ closure B :=
    (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact And.intro hxA hxB

theorem IsClosed.compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : IsOpen Aᶜ := by
  simpa [isOpen_compl_iff] using (isOpen_compl_iff).2 hA

theorem Topology.interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ∩ closure A = interior A := by
  ext x
  constructor
  · intro h
    exact h.1
  · intro hxInt
    have hxA : (x : X) ∈ A := interior_subset hxInt
    have hxCl : (x : X) ∈ closure A := subset_closure hxA
    exact And.intro hxInt hxCl

theorem Topology.P2_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior (closure (interior A))) hOpen

theorem Topology.interior_closure_eq_self_of_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) → interior (closure A) = closure A := by
  intro hP2
  -- `P2` for `closure A` is equivalent to `IsOpen (closure A)`.
  have hOpen : IsOpen (closure A) :=
    (Topology.P2_closure_iff_open_closure (X := X) (A := A)).1 hP2
  -- For an open set, its interior equals itself.
  exact
    (Topology.isOpen_closure_iff_interior_eq_self (X := X) (A := A)).1 hOpen

theorem Topology.closure_interior_closure_inter_subset_inter_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∩ B))) ⊆
      closure (interior (closure A)) ∩ closure (interior (closure B)) := by
  intro x hx
  -- `closure (A ∩ B) ⊆ closure A`
  have h_cl_subset_left : closure (A ∩ B) ⊆ closure A :=
    closure_mono Set.inter_subset_left
  -- Hence `interior (closure (A ∩ B)) ⊆ interior (closure A)`
  have h_int_subset_left :
      interior (closure (A ∩ B)) ⊆ interior (closure A) :=
    interior_mono h_cl_subset_left
  -- Taking closures preserves this inclusion
  have h_cl_int_subset_left :
      closure (interior (closure (A ∩ B))) ⊆
        closure (interior (closure A)) :=
    closure_mono h_int_subset_left
  -- Obtain the left component of the goal
  have hx_left : x ∈ closure (interior (closure A)) :=
    h_cl_int_subset_left hx
  -- The corresponding statements for `B`
  have h_cl_subset_right : closure (A ∩ B) ⊆ closure B :=
    closure_mono Set.inter_subset_right
  have h_int_subset_right :
      interior (closure (A ∩ B)) ⊆ interior (closure B) :=
    interior_mono h_cl_subset_right
  have h_cl_int_subset_right :
      closure (interior (closure (A ∩ B))) ⊆
        closure (interior (closure B)) :=
    closure_mono h_int_subset_right
  have hx_right : x ∈ closure (interior (closure B)) :=
    h_cl_int_subset_right hx
  -- Combine the two components
  exact And.intro hx_left hx_right

theorem Topology.closure_inter_interior_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure A ∩ interior A : Set X) = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    have hxCl : x ∈ closure A := subset_closure hxA
    exact And.intro hxCl hxInt

@[simp] theorem Topology.closure_interior_closure_interior_simp
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  simpa using
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)

theorem Topology.closure_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (∅ : Set X) ↔ A = (∅ : Set X) := by
  constructor
  · intro h
    -- Show that `A` is contained in `∅`.
    have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure A := subset_closure hx
      simpa [h] using this
    -- Combine the two inclusions to obtain the equality.
    apply Set.Subset.antisymm h_subset
    intro x hx
    exact hx.elim
  · intro h
    simpa [h, closure_empty]

theorem Topology.inter_closure_interior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∩ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  -- `x` lies in `closure (interior A)`.
  have hxA : x ∈ closure (interior A) := hx.1
  -- `interior A` is contained in `interior (A ∪ B)`.
  have h_int_subset : interior A ⊆ interior (A ∪ B) := by
    have h_sub : (A : Set X) ⊆ A ∪ B := by
      intro y hy; exact Or.inl hy
    exact interior_mono h_sub
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono h_int_subset
  -- Transport the membership of `x`.
  exact h_closure_subset hxA

theorem Topology.P2_closure_interior_iff_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior A)) ↔
      Topology.P3 (X := X) (closure (interior A)) := by
  have h₁ :=
    Topology.P2_closure_interior_iff_open_closure_interior
      (X := X) (A := A)
  have h₂ :=
    Topology.P3_closure_interior_iff_open_closure_interior
      (X := X) (A := A)
  exact h₁.trans h₂.symm

theorem Topology.interior_closure_union_eq_interior_union_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure (A ∪ B)) = interior (A ∪ B) := by
  -- The union of two closed sets is closed.
  have hClosedUnion : IsClosed (A ∪ B : Set X) := hA.union hB
  -- For a closed set, its closure is itself.
  have hClosureEq : closure (A ∪ B : Set X) = A ∪ B := hClosedUnion.closure_eq
  -- Rewrite using the equality obtained above.
  simpa [hClosureEq]

theorem Topology.P2_iterate_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      Topology.P2 (X := X)
        (((fun S : Set X => interior (closure S))^[n.succ]) A) := by
  intro n
  -- Define the iteration function for clarity.
  let f : Set X → Set X := fun S => interior (closure S)
  -- Apply the lemma `P2_interior_closure` to the `n`-th iterate.
  have hP2 :
      Topology.P2 (X := X) (interior (closure ((f^[n]) A))) :=
    Topology.P2_interior_closure (X := X) (A := (f^[n]) A)
  -- Rewrite using the definition of the `(n.succ)`-th iterate.
  simpa [f, Function.iterate_succ_apply'] using hP2

theorem Topology.closure_inter_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure A ∩ closure (interior A) : Set X) = closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    -- `closure (interior A)` is contained in `closure A`
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    have hx_closureA : x ∈ closure A := h_subset hx
    exact And.intro hx_closureA hx

theorem Topology.isOpen_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A ↔ interior A = A := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro h_eq
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using hOpenInt

theorem Topology.closure_interior_union_eq_univ_of_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h_dense : closure (interior B) = (Set.univ : Set X)) :
    closure (interior (A ∪ B)) = (Set.univ : Set X) := by
  simpa [Set.union_comm] using
    (Topology.closure_interior_union_eq_univ_of_dense_left
      (X := X) (A := B) (B := A) h_dense)

theorem Topology.closed_P123_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A) ↔
      IsOpen A := by
  constructor
  · rintro ⟨_, _, hP3⟩
    exact Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  · intro hOpen
    exact
      Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A) hOpen


theorem Topology.interior_closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (∅ : Set X) ↔
      interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`
    have hsubset :
        interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (X := X) (A := A)
    -- Show that `interior A` has no elements.
    refine Set.eq_empty_iff_forall_not_mem.2 ?_
    intro x hxIntA
    have : (x : X) ∈ interior (closure (interior A)) := hsubset hxIntA
    simpa [h] using this
  · intro hIntEmpty
    -- From `interior A = ∅` we get `closure (interior A) = ∅`.
    have hClIntEmpty : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty]
    -- Hence its interior is also empty.
    simpa [hClIntEmpty] using by
      simp [hClIntEmpty]

theorem Topology.closure_inter_closed_left_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hClosed : IsClosed A) :
    closure (A ∩ B : Set X) ⊆ A ∩ closure B := by
  intro x hx
  have hxA : x ∈ A := by
    -- Since `A ∩ B ⊆ A`, taking closures gives
    -- `closure (A ∩ B) ⊆ closure A = A` (because `A` is closed).
    have h_subset : closure (A ∩ B : Set X) ⊆ A := by
      have h_temp : closure (A ∩ B : Set X) ⊆ closure A :=
        closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
      simpa [hClosed.closure_eq] using h_temp
    exact h_subset hx
  have hxB : x ∈ closure B := by
    -- Monotonicity of `closure` for the inclusion `A ∩ B ⊆ B`.
    have h_subset : closure (A ∩ B : Set X) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact h_subset hx
  exact And.intro hxA hxB

theorem Topology.closure_inter_eq_self_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B : Set X) = A ∩ B := by
  have hClosed : IsClosed (A ∩ B : Set X) := hA.inter hB
  simpa using hClosed.closure_eq

theorem Topology.P1_closure_iff_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure A) ↔
      closure A ⊆ closure (interior (closure A)) := by
  simpa using
    (Topology.P1_iff_closure_subset_closure_interior
      (X := X) (A := closure A))

theorem Topology.closure_diff_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A := by
  -- `A \ B` is contained in `A`, so the monotonicity of `closure` gives the result.
  exact closure_mono (by
    intro x hx
    exact hx.1)

theorem Topology.eq_closure_interior_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = A) : Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hxA
  simpa [h] using hxA

theorem Topology.P3_iterate_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      Topology.P3 (X := X)
        (((fun S : Set X => interior (closure S))^[n.succ]) A) := by
  intro n
  -- Define the operator `f : Set X → Set X` as `S ↦ interior (closure S)`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- The `(n.succ)`-th iterate of `f` applied to `A` is an open set,
  -- namely `interior (closure ((f^[n]) A))`.
  have hOpen : IsOpen (interior (closure ((f^[n]) A))) := isOpen_interior
  -- Every open set satisfies `P3`.
  have hP3 : Topology.P3 (X := X) (interior (closure ((f^[n]) A))) :=
    Topology.isOpen_implies_P3
      (X := X) (A := interior (closure ((f^[n]) A))) hOpen
  -- Rewrite to match the desired form and conclude.
  simpa [f, Function.iterate_succ_apply'] using hP3

theorem Topology.closure_interior_inter_closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A) ∩ closure (interior (closure A)) : Set X) =
      closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hsubset :
        closure (interior A) ⊆ closure (interior (closure A)) :=
      Topology.closure_interior_subset_closure_interior_closure (X := X) (A := A)
    have hx' : x ∈ closure (interior (closure A)) := hsubset hx
    exact And.intro hx hx'

theorem Topology.closure_interior_minimal_closed
    {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hC : IsClosed C) (h_sub : interior A ⊆ C) :
    closure (interior A) ⊆ C := by
  have h₁ : closure (interior A) ⊆ closure C := closure_mono h_sub
  simpa [hC.closure_eq] using h₁

@[simp] theorem Topology.closure_interior_closure_interior_closure_interior_simp
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  simpa using
    (Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A))

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, regard `x` as an element of `closure (interior A)`.
  have hx' : x ∈ closure (interior A) := interior_subset hx
  -- Use the existing inclusion on closures to conclude.
  have h_subset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure
      (X := X) (A := A)
  exact h_subset hx'

theorem Topology.interior_diff_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A \ interior A : Set X) = (∅ : Set X) := by
  -- We prove that `interior (A \ interior A)` has no points.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxIntDiff
  -- `x` lies in `A \ interior A`.
  have hxDiff : x ∈ (A \ interior A : Set X) := interior_subset hxIntDiff
  -- Any open subset of `A` is contained in `interior A`.
  have h_subsetA : interior (A \ interior A : Set X) ⊆ A := by
    intro y hy
    exact (interior_subset hy).1
  have h_to_intA : interior (A \ interior A : Set X) ⊆ interior A :=
    interior_maximal h_subsetA isOpen_interior
  have hxIntA : x ∈ interior A := h_to_intA hxIntDiff
  -- Contradiction: `x` is both in and not in `interior A`.
  exact (hxDiff.2 hxIntA)

theorem Topology.closure_inter_closed_right_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hClosed : IsClosed B) :
    closure (A ∩ B : Set X) ⊆ closure A ∩ B := by
  intro x hx
  -- First, `x ∈ closure A` because `A ∩ B ⊆ A`.
  have hxA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  -- Next, since `B` is closed and `A ∩ B ⊆ B`, we get `x ∈ B`.
  have hxB : x ∈ B := by
    have h_subset : closure (A ∩ B : Set X) ⊆ B := by
      -- Use the fact that `closure B = B` for a closed set `B`.
      have h_temp :
          closure (A ∩ B : Set X) ⊆ closure B :=
        closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
      simpa [hClosed.closure_eq] using h_temp
    exact h_subset hx
  exact And.intro hxA hxB

theorem Topology.nonempty_of_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure A)).Nonempty → A.Nonempty := by
  rintro ⟨x, hxInt⟩
  -- `x` lies in `closure A`.
  have hxCl : x ∈ closure A := interior_subset hxInt
  -- The set `interior (closure A)` is an open neighbourhood of `x`
  -- contained in `closure A`.
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  -- By the characterization of points in the closure, this neighbourhood
  -- meets `A`, providing the desired element.
  rcases (mem_closure_iff.1 hxCl) (interior (closure A)) hOpen hxInt with
    ⟨y, _, hyA⟩
  exact ⟨y, hyA⟩

theorem Topology.closure_interior_closure_interior_eq_closure_interior_simple
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have : closure (interior (closure (interior A))) ⊆
        closure (interior A) := by
      -- This is an instance of `closure (interior (closure B)) ⊆ closure B`
      -- with `B = interior A`.
      simpa using
        (Topology.closure_interior_closure_subset_closure
          (X := X) (A := interior A))
    exact this
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior
        (X := X) (A := A)
    exact closure_mono this

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hxInt
  -- A point in the interior of `A` certainly lies in `A`.
  have hxA : (x : X) ∈ A := interior_subset hxInt
  -- Every point of `A` is in the closure of `A`.
  exact subset_closure hxA

theorem Topology.interior_eq_closure_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior A = closure A) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  -- From the hypothesis we know that `A` is both open and closed.
  have hOpen : IsOpen A :=
    (Topology.open_and_closed_of_interior_eq_closure (X := X) (A := A) h).1
  -- Any open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A) hOpen

theorem Topology.interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B : Set X) = A ∩ interior B := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx_intB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    have hx_AB : x ∈ (A ∩ B : Set X) := interior_subset hx
    exact And.intro hx_AB.1 hx_intB
  · intro x hx
    rcases hx with ⟨hxA, hx_intB⟩
    -- The set `A ∩ interior B` is open and contains `x`
    have h_open : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact And.intro hy.1 (interior_subset hy.2)
    have hx_mem : x ∈ (A ∩ interior B : Set X) := And.intro hxA hx_intB
    exact
      mem_interior.2
        ⟨A ∩ interior B, h_subset, h_open, hx_mem⟩

theorem Topology.interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simp [closure_empty, interior_empty]

theorem Topology.closure_diff_subset_closure_diffInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A \ interior B := by
  intro x hx
  -- First, `x` lies in `closure A` because `A \ B ⊆ A`.
  have hxClA : x ∈ closure A := by
    have hSub : (A \ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact (closure_mono hSub) hx
  -- Next, show that `x` is **not** in `interior B`.
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- Use the characterization of points in the closure.
    have hNonEmpty :
        ((interior B) ∩ (A \ B) : Set X).Nonempty :=
      (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
    rcases hNonEmpty with ⟨y, hyIntB, hyAminusB⟩
    -- From `y ∈ interior B`, we get `y ∈ B`.
    have : (y : X) ∈ B := interior_subset hyIntB
    -- But `y ∉ B` because `y ∈ A \ B`, contradiction.
    exact (hyAminusB.2 this).elim
  exact And.intro hxClA hxNotIntB

theorem Topology.closure_interior_inter_closure_subset_inter_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ closure B)) ⊆
      closure (interior A) ∩ closure (interior (closure B)) := by
  intro x hx
  -- `interior (A ∩ closure B)` is contained in `interior A`
  have h_left : interior (A ∩ closure B) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ closure B : Set X) ⊆ A)
  -- Hence `x ∈ closure (interior A)`
  have hx_left : x ∈ closure (interior A) :=
    (closure_mono h_left) hx
  -- Similarly, `interior (A ∩ closure B)` is contained in `interior (closure B)`
  have h_right : interior (A ∩ closure B) ⊆ interior (closure B) := by
    have h_sub : (A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact interior_mono h_sub
  -- Thus `x ∈ closure (interior (closure B))`
  have hx_right : x ∈ closure (interior (closure B)) :=
    (closure_mono h_right) hx
  exact And.intro hx_left hx_right

theorem IsOpen.compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : IsClosed (Aᶜ) := by
  simpa using ((isClosed_compl_iff).2 hA)

theorem Topology.interior_closure_interior_eq_univ_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (Set.univ : Set X) ↔
      closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- `closure (interior A) ⊆ univ` is obvious.
    have h₁ : closure (interior A) ⊆ (Set.univ : Set X) := by
      intro _ _; simp
    -- `univ ⊆ closure (interior A)` follows from the hypothesis.
    have h₂ : (Set.univ : Set X) ⊆ closure (interior A) := by
      intro x _
      have hxInt : (x : X) ∈ interior (closure (interior A)) := by
        simpa [hInt] using (by simp : (x : X) ∈ (Set.univ : Set X))
      exact (interior_subset : interior (closure (interior A)) ⊆
          closure (interior A)) hxInt
    exact subset_antisymm h₁ h₂
  · intro hCl
    exact
      Topology.interior_closure_interior_eq_univ_of_dense_interior
        (X := X) (A := A) hCl

theorem Topology.interior_union_closure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior A ∪ closure A : Set X) = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxInt =>
        -- From `x ∈ interior A`, we get `x ∈ A`, hence `x ∈ closure A`.
        have : (x : X) ∈ A := interior_subset hxInt
        exact subset_closure this
    | inr hxCl =>
        exact hxCl
  · intro hxCl
    exact Or.inr hxCl

theorem Topology.interior_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  have hA : (x : X) ∈ A := interior_subset hx.1
  have hAc : (x : X) ∈ Aᶜ := interior_subset hx.2
  exact hAc hA

theorem Topology.isOpen_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) : (A : Set X) ⊆ interior (closure A) := by
  -- Since `A` is open, its interior is itself.
  have hInt : interior A = A := hOpen.interior_eq
  -- Monotonicity of `interior` yields `interior A ⊆ interior (closure A)`.
  have hSubset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  -- Rewrite with `hInt` to obtain the desired inclusion.
  simpa [hInt] using hSubset

theorem Topology.interior_closure_inter_eq_interior_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure (A ∩ B)) = interior (A ∩ B) := by
  -- Since both `A` and `B` are closed, so is their intersection.
  have hClosed : IsClosed (A ∩ B : Set X) := hA.inter hB
  -- For a closed set, its closure is itself.
  have h_closure_eq : closure (A ∩ B : Set X) = A ∩ B := hClosed.closure_eq
  -- Rewrite using the obtained equality.
  simpa [h_closure_eq]

theorem Topology.P1_iterate_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      Topology.P1 (X := X)
        (((fun S : Set X => interior (closure S))^[n.succ]) A) := by
  intro n
  -- Define the operator `f : Set X → Set X`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- The `(n.succ)`-th iterate of `f` applied to `A` is the open set
  -- `interior (closure ((f^[n]) A))`.
  have hOpen : IsOpen (interior (closure ((f^[n]) A))) := isOpen_interior
  -- Any open set satisfies `P1`.
  have hP1 : Topology.P1 (X := X) (interior (closure ((f^[n]) A))) :=
    Topology.isOpen_implies_P1
      (X := X) (A := interior (closure ((f^[n]) A))) hOpen
  -- Rewrite to match the desired form.
  simpa [f, Function.iterate_succ_apply'] using hP1



theorem Topology.closure_interior_closure_union_eq_closure_interior_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∪ B))) =
      closure (interior (closure A ∪ closure B)) := by
  simpa [closure_union]

theorem Topology.union_interior_closure_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Step 1: `interior A ⊆ interior (A ∪ B)`
      have h_int_subset : interior A ⊆ interior (A ∪ B) := by
        have h_sub : A ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact interior_mono h_sub
      -- Step 2: `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      -- Step 3: apply `interior_mono`
      have h_int_closure_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      exact h_int_closure_subset hxA
  | inr hxB =>
      -- The same three steps with `B` instead of `A`.
      have h_int_subset : interior B ⊆ interior (A ∪ B) := by
        have h_sub : B ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono h_sub
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      have h_int_closure_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      exact h_int_closure_subset hxB

theorem _root_.IsOpen.compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : IsClosed (Aᶜ) := by
  simpa [isClosed_compl_iff] using (isClosed_compl_iff).2 hA

theorem Topology.interior_closure_interior_eq_univ_of_dense_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X))
    (hP1 : Topology.P1 (X := X) A) :
    interior (closure (interior A)) = (Set.univ : Set X) := by
  -- From `P1`, the two closures coincide.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  -- Rewrite using both equalities and simplify.
  calc
    interior (closure (interior A)) = interior (closure A) := by
      simpa [h_eq]
    _ = interior (Set.univ : Set X) := by
      simpa [h_dense]
    _ = (Set.univ : Set X) := by
      simpa [interior_univ]

theorem Topology.P3_closure_implies_P1_and_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) →
      (Topology.P1 (X := X) (closure A) ∧
        Topology.P2 (X := X) (closure A)) := by
  intro hP3
  have hP1 : Topology.P1 (X := X) (closure A) :=
    Topology.P3_closure_implies_P1_closure (X := X) (A := A) hP3
  have hP2 : Topology.P2 (X := X) (closure A) :=
    Topology.P3_closure_implies_P2_closure (X := X) (A := A) hP3
  exact And.intro hP1 hP2

theorem Topology.interior_closure_union_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hxInt =>
      exact (interior_subset : interior (closure A) ⊆ closure A) hxInt
  | inr hxCl =>
      exact
        (Topology.closure_interior_subset_closure (X := X) (A := A)) hxCl

theorem Topology.interior_closure_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ⊆ interior (closure (A ∪ B)) := by
  -- `A ⊆ A ∪ B`
  have hA : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  -- Hence `closure A ⊆ closure (A ∪ B)`
  have hCl : closure A ⊆ closure (A ∪ B) := closure_mono hA
  -- Apply monotonicity of `interior`
  exact interior_mono hCl

theorem Topology.interior_inter_closure_compl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior A ∩ closure (Aᶜ) : Set X) = (∅ : Set X) := by
  -- We show that the intersection contains no points.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hxInt, hxClCompl⟩
  -- `interior A` is an open neighbourhood of `x` contained in `A`.
  have hOpen : IsOpen (interior A) := isOpen_interior
  -- Since `x ∈ closure (Aᶜ)`, every such neighbourhood meets `Aᶜ`.
  have hNonempty :=
    (mem_closure_iff.1 hxClCompl) (interior A) hOpen hxInt
  rcases hNonempty with ⟨y, ⟨hyInt, hyCompl⟩⟩
  -- But `interior A ⊆ A`, so `y ∈ A`, contradicting `y ∈ Aᶜ`.
  exact hyCompl (interior_subset hyInt)

theorem Topology.closure_interior_subset_self_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    closure (interior A) ⊆ A := by
  -- First, `interior A` is contained in `A`.
  have h₁ : interior A ⊆ A := interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
  -- Since `A` is closed, `closure A = A`; rewrite and conclude.
  simpa [hClosed.closure_eq] using h₂



theorem Topology.closure_interior_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simpa [interior_empty, closure_empty]

theorem Topology.open_and_closed_iff_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (IsOpen A ∧ IsClosed A) ↔ interior A = closure A := by
  constructor
  · rintro ⟨hOpen, hClosed⟩
    have hInt : interior A = A := hOpen.interior_eq
    have hCl : closure A = A := hClosed.closure_eq
    simpa [hInt, hCl]
  · intro h_eq
    exact
      Topology.open_and_closed_of_interior_eq_closure
        (X := X) (A := A) h_eq

theorem Topology.interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We will use the characterization `mem_closure_iff`.
  -- It suffices to show that every open neighbourhood `U` of `x`
  -- meets `A ∩ B`.
  refine (mem_closure_iff).2 ?_
  intro U hUopen hxU
  -- Consider `U ∩ interior A`, an open neighbourhood of `x`
  -- contained in `A`.
  have hU_intA_open : IsOpen (U ∩ interior A) := hUopen.inter isOpen_interior
  have hxU_intA : x ∈ (U ∩ interior A) := And.intro hxU hxIntA
  -- Since `x ∈ closure B`, this neighbourhood intersects `B`.
  have h_nonempty : ((U ∩ interior A) ∩ B).Nonempty :=
    (mem_closure_iff.1 hxClB) (U ∩ interior A) hU_intA_open hxU_intA
  -- Extract a point `y` witnessing the intersection.
  rcases h_nonempty with ⟨y, ⟨hyU_intA, hyB⟩⟩
  -- From `y ∈ U ∩ interior A` we get `y ∈ U` and `y ∈ A`.
  have hyU : y ∈ U := hyU_intA.1
  have hyA : y ∈ A := interior_subset hyU_intA.2
  -- Thus `y ∈ U ∩ (A ∩ B)`, as required.
  exact ⟨y, And.intro hyU (And.intro hyA hyB)⟩

theorem Topology.isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure A \ interior A : Set X) := by
  -- `closure A` is closed.
  have hClosedClosure : IsClosed (closure A) := isClosed_closure
  -- The complement of the open set `interior A` is closed.
  have hClosedComplInt : IsClosed ((interior A)ᶜ) := by
    simpa using (isClosed_compl_iff).2 (isOpen_interior (A := A))
  -- Express the difference as an intersection and use `IsClosed.inter`.
  simpa [Set.diff_eq] using hClosedClosure.inter hClosedComplInt

theorem Topology.closure_interior_inter_eq_closure_inter_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- For open sets, taking the interior leaves the set unchanged.
  have hInt : interior (A ∩ B) = A ∩ B :=
    (Topology.interior_inter_eq_of_open (X := X) (A := A) (B := B) hA hB)
  simpa [hInt]

theorem Topology.P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → A ⊆ interior (closure A) := by
  intro hP2 x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hSubset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure (X := X) (A := A)
  exact hSubset hxInt

theorem Topology.P3_of_interior_closure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure A) = closure A) :
    Topology.P3 (X := X) A := by
  -- From the equality we obtain that `closure A` is open.
  have hOpen : IsOpen (closure A) :=
    (Topology.isOpen_closure_iff_interior_eq_self (X := X) (A := A)).mpr h
  -- An open closure of `A` implies `P3 A`.
  exact Topology.P3_of_open_closure (X := X) (A := A) hOpen

theorem Topology.closure_subset_closure_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (B : Set X) ⊆ interior (closure A)) :
    closure B ⊆ closure A := by
  -- First, take closures on both sides of the inclusion `h`.
  have h₁ : closure B ⊆ closure (interior (closure A)) :=
    closure_mono h
  -- Next, use the fact that `interior (closure A) ⊆ closure A`.
  have h₂ : closure (interior (closure A)) ⊆ closure A := by
    have : interior (closure A) ⊆ closure A := interior_subset
    have h_cl : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono this
    simpa [closure_closure] using h_cl
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem Set.nonempty_univ {α : Type*} [h : Nonempty α] :
    (Set.univ : Set α).Nonempty := by
  classical
  rcases h with ⟨x⟩
  exact ⟨x, by simp⟩

theorem Topology.interior_closure_inter_closure_subset_closure_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∩ closure B ⊆ closure (closure A ∩ B) := by
  simpa using
    (Topology.interior_inter_closure_subset_closure_inter
      (X := X) (A := closure A) (B := B))

theorem Topology.interior_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ closure (interior A) := by
  intro x hxInt
  exact subset_closure hxInt

theorem Topology.closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- `hxA` : x ∈ closure A
  -- `hxNotB` : x ∉ closure B
  have hClosureA := (mem_closure_iff).1 hxA
  -- The complement of `closure B` is an open neighbourhood of `x`.
  have hOpenT : IsOpen ((closure B)ᶜ : Set X) :=
    isClosed_closure.isOpen_compl
  have hxT : x ∈ (closure B)ᶜ := hxNotB
  -- Show that every open neighbourhood of `x` meets `A \ B`.
  refine (mem_closure_iff).2 ?_
  intro U hUopen hxU
  -- Consider `U ∩ (closure B)ᶜ`, an open neighbourhood of `x`.
  have hVopen : IsOpen (U ∩ (closure B)ᶜ) := hUopen.inter hOpenT
  have hxV : x ∈ U ∩ (closure B)ᶜ := And.intro hxU hxT
  -- Since `x ∈ closure A`, this neighbourhood meets `A`.
  have hNonempty := hClosureA (U ∩ (closure B)ᶜ) hVopen hxV
  rcases hNonempty with ⟨y, ⟨hyU, hyT⟩, hyA⟩
  -- `y` is in `A` and not in `closure B`, hence not in `B`.
  have hyNotB : (y : X) ∉ B := by
    intro hyB
    have : (y : X) ∈ closure B := subset_closure hyB
    exact hyT this
  have hyInDiff : (y : X) ∈ A \ B := And.intro hyA hyNotB
  -- Thus `y` lies in `U ∩ (A \ B)`.
  exact ⟨y, And.intro hyU hyInDiff⟩



theorem Topology.interior_nonempty_iff_exists_open_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty ↔
      ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ U.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨interior A, isOpen_interior, interior_subset, ⟨x, hx⟩⟩
  · rintro ⟨U, hUopen, hUsub, ⟨x, hxU⟩⟩
    have hUsubInt : U ⊆ interior A :=
      interior_maximal hUsub hUopen
    exact ⟨x, hUsubInt hxU⟩

theorem Topology.closure_interior_iterate_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      closure (interior (((fun S : Set X => closure (interior S))^[n]) A)) =
        closure (interior A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Function.iterate_succ_apply',
        Topology.closure_interior_closure_interior_eq_closure_interior, ih]

theorem Topology.interior_compl_eq_empty_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We prove that `interior (Aᶜ)` contains no points.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxInt
  -- Since `closure A = univ`, every point is in `closure A`.
  have hxCl : (x : X) ∈ closure A := by
    simpa [h_dense] using (by
      have : (x : X) ∈ (Set.univ : Set X) := by simp
      exact this)
  -- `interior (Aᶜ)` is an open neighbourhood of `x`.
  have hOpen : IsOpen (interior (Aᶜ)) := isOpen_interior
  -- By density, this neighbourhood meets `A`.
  have hNonempty : ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
    (mem_closure_iff.1 hxCl) (interior (Aᶜ)) hOpen hxInt
  rcases hNonempty with ⟨y, hyInt, hyA⟩
  -- But `interior (Aᶜ)` is contained in `Aᶜ`, so `y ∉ A`, contradiction.
  have hNotA : (y : X) ∈ (Aᶜ : Set X) := interior_subset hyInt
  exact hNotA hyA



theorem Topology.closure_inter_open_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : (closure A ∩ A : Set X) = A := by
  -- Start with the general identity `closure A ∩ interior A = interior A`.
  have h :=
    Topology.closure_inter_interior_eq_interior (X := X) (A := A)
  -- Rewrite `interior A` using the openness of `A`.
  simpa [hA.interior_eq] using h

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (∅ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  cases hx

theorem Topology.interior_closure_inter_subset_inter_interior_closure_leftInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Left component: `x ∈ interior (closure A)`
  have hx_left : x ∈ interior (closure A) := by
    -- Since `A ∩ interior B ⊆ A`, taking closures yields the desired inclusion.
    have h_cl_sub : closure (A ∩ interior B) ⊆ closure A := by
      apply closure_mono
      intro y hy
      exact hy.1
    exact (interior_mono h_cl_sub) hx
  -- Right component: `x ∈ interior (closure B)`
  have hx_right : x ∈ interior (closure B) := by
    -- Use `interior B ⊆ B` to show `A ∩ interior B ⊆ B`.
    have h_cl_sub : closure (A ∩ interior B) ⊆ closure B := by
      apply closure_mono
      intro y hy
      exact
        (interior_subset : interior B ⊆ B) hy.2
    exact (interior_mono h_cl_sub) hx
  exact And.intro hx_left hx_right

theorem Topology.closure_nonempty_iff_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A) : Set X).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hCl
    rcases hCl with ⟨x, hxCl⟩
    -- Using the characterization of points in the closure with the open set `univ`.
    have hInt : ((Set.univ : Set X) ∩ A).Nonempty := by
      have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
      have hxU : (x : X) ∈ (Set.univ : Set X) := by
        simp
      exact (mem_closure_iff).1 hxCl (Set.univ) hOpen hxU
    rcases hInt with ⟨y, ⟨_, hyA⟩⟩
    exact ⟨y, hyA⟩
  · rintro ⟨x, hxA⟩
    exact ⟨x, subset_closure hxA⟩

theorem Topology.interior_inter_interior_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ interior B) = interior A ∩ interior B := by
  have hOpen : IsOpen (interior B) := isOpen_interior
  simpa using
    (Topology.interior_inter_open_right (X := X) (A := A) (B := interior B) hOpen)

theorem Topology.P2_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure A)) :=
  Topology.P2_interior_closure (X := X) (A := A)

theorem Topology.not_P3_of_nonempty_emptyInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : A.Nonempty)
    (hIntEmpty : interior (closure A) = (∅ : Set X)) :
    ¬ Topology.P3 (X := X) A := by
  intro hP3
  -- From `P3` and the hypothesis on the interior we deduce `A = ∅`.
  have hAempty :
      A = (∅ : Set X) :=
    Topology.P3_emptyInteriorClosure_implies_empty
      (X := X) (A := A) hP3 hIntEmpty
  -- But `A` was assumed nonempty—contradiction.
  have hNonemptyEmpty : (∅ : Set X).Nonempty := by
    simpa [hAempty] using hA
  cases hNonemptyEmpty with
  | intro x hx =>
      cases hx

theorem Topology.P1_union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hP1A : Topology.P1 (X := X) A) (hOpenU : IsOpen U) :
    Topology.P1 (X := X) (A ∪ U) := by
  have hP1U : Topology.P1 (X := X) U :=
    Topology.isOpen_implies_P1 (X := X) (A := U) hOpenU
  exact
    Topology.P1_union (X := X) (A := A) (B := U) hP1A hP1U

theorem Topology.interior_closure_subset_interior_closure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  simpa [Set.union_comm] using
    (Topology.interior_closure_subset_interior_closure_union_left
      (X := X) (A := B) (B := A))

theorem Topology.closure_interior_closure_interior_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A →
      closure (interior (closure (interior A))) = closure A := by
  intro hP2
  have h₁ :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  have h₂ : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P2 (X := X) (A := A) hP2
  simpa [h₂] using h₁

theorem Topology.closure_interior_diff_subset_closure_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) \ interior B := by
  classical
  intro x hx
  -- `interior (A \ B) ⊆ interior A`
  have hInt : interior (A \ B) ⊆ interior A := by
    have : (A \ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact interior_mono this
  -- Hence `x ∈ closure (interior A)`
  have hx₁ : x ∈ closure (interior A) :=
    (closure_mono hInt) hx
  -- Show that `x ∉ interior B`
  have hx₂ : x ∉ interior B := by
    intro hxIntB
    -- Use the characterization of points in the closure
    have hOpen : IsOpen (interior B) := isOpen_interior
    have hNonempty :
        ((interior B) ∩ interior (A \ B) : Set X).Nonempty :=
      (mem_closure_iff.1 hx) (interior B) hOpen hxIntB
    rcases hNonempty with ⟨y, ⟨hyIntB, hyIntDiff⟩⟩
    -- Contradiction: `y ∈ B` and `y ∉ B`
    have hInB : (y : X) ∈ B := interior_subset hyIntB
    have hInDiff : (y : X) ∈ A \ B := interior_subset hyIntDiff
    exact (hInDiff.2 hInB)
  exact And.intro hx₁ hx₂

theorem Topology.closure_interior_closure_subset_self_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    closure (interior (closure A)) ⊆ A := by
  -- `interior (closure A)` is contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Since `A` is closed, its closure is itself, and `closure (closure A)` simplifies.
  simpa [closure_closure, hClosed.closure_eq] using h₂

theorem Topology.closure_interior_nonempty_of_interior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (interior A : Set X).Nonempty → (closure (interior A) : Set X).Nonempty := by
  rintro ⟨x, hxInt⟩
  exact ⟨x, subset_closure hxInt⟩

theorem Topology.closure_iInter_subset_iInter_closure
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (⋂ i, A i : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- Show that `x` belongs to `closure (A i)` for each `i`.
  have hx_i : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The inclusion `(⋂ j, A j) ⊆ A i` follows from the definition of `⋂`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `closure` transports the inclusion.
    have h_closure_subset :
        closure (⋂ j, A j : Set X) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure_subset hx
  -- Combine the coordinate-wise membership into an intersection.
  exact Set.mem_iInter.2 hx_i

theorem Topology.interior_closure_diff_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior ((closure A) \ A : Set X) = (∅ : Set X) := by
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxInt
  have hxDiff : (x : X) ∈ (closure A \ A : Set X) := by
    exact interior_subset hxInt
  have hxCl : x ∈ closure A := hxDiff.1
  -- Consider the open neighbourhood `interior (closure A \ A)` of `x`.
  have h_open :
      IsOpen (interior ((closure A) \ A : Set X)) := isOpen_interior
  -- By density of `A` in its closure, this neighbourhood meets `A`.
  have h_nonempty :
      ((interior ((closure A) \ A : Set X)) ∩ A : Set X).Nonempty :=
    (mem_closure_iff.1 hxCl) _ h_open hxInt
  rcases h_nonempty with ⟨y, ⟨hyInt, hyA⟩⟩
  -- But each point of `interior (closure A \ A)` lies outside `A`.
  have h_subset :
      (interior ((closure A) \ A : Set X) : Set X) ⊆ (closure A \ A) :=
    interior_subset
  have hyNotA : (y : X) ∉ A := (h_subset hyInt).2
  exact hyNotA hyA



theorem Topology.closed_P1_interior_closure_interior_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP1 : Topology.P1 (X := X) A) :
    interior (closure (interior A)) = interior A := by
  -- First, use the general lemma that relates `P1` to interiors of closures.
  have h_eq :=
    Topology.interior_closure_interior_eq_interior_closure_of_P1
      (X := X) (A := A) hP1
  -- Since `A` is closed, its closure is itself. Substitute to conclude.
  simpa [hClosed.closure_eq] using h_eq