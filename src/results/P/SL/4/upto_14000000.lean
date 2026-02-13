

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P3]
  intro x hxA
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_subset : closure (interior A) ⊆ closure A := by
      have h_int_subset : interior A ⊆ A := interior_subset
      exact closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact h_subset hx_in

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P1]
  intro x hxA
  exact interior_subset (hP2 hxA)

theorem P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have h : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using h

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  intro x hx
  -- `interior A` is contained in its closure
  have h_sub : interior A ⊆ closure (interior A) := by
    intro y hy
    exact subset_closure hy
  -- Taking interiors preserves the inclusion
  have h_inclusion : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h_sub
  -- Rewrite `interior (interior A)` and apply the inclusion to `x`
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  have hx'' : x ∈ interior (closure (interior A)) := h_inclusion hx'
  simpa using hx''

theorem P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact And.intro (Topology.P2_imp_P1 hP2) (Topology.P2_imp_P3 hP2)

theorem interior_closure_interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  intro x hx
  -- First, note that `closure (interior A)` is contained in `closure A`
  have h_closure_subset : closure (interior A) ⊆ closure A := by
    have h_int_subset : interior A ⊆ A := interior_subset
    exact closure_mono h_int_subset
  -- Taking interiors preserves this inclusion
  have h_interiors : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  -- Apply the inclusion to the given point `x`
  exact h_interiors hx

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  have hx_closure : x ∈ closure (interior A) := interior_subset hx
  have h_closure_subset : closure (interior A) ⊆ closure A := by
    have h_int_subset : interior A ⊆ A := interior_subset
    exact closure_mono h_int_subset
  exact h_closure_subset hx_closure

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) : closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  have hP2 : Topology.P2 (interior A) := P2_interior A
  exact P2_imp_P3 (A := interior A) hP2

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure A = closure (interior A) := by
  intro hP1
  apply subset_antisymm
  · have : closure A ⊆ closure (closure (interior A)) := by
      exact closure_mono hP1
    simpa using this
  · exact closure_mono interior_subset

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) : interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    exact closure_eq_closure_interior_of_P1 hP1
  · intro h_eq
    dsimp [Topology.P1]
    intro x hx
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq] using this

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure A = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_imp_P1 (A := A) hP2
  exact Topology.closure_eq_closure_interior_of_P1 hP1

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure A) := by
  exact interior_mono subset_closure

theorem isOpen_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have h_int_eq : interior A = A := hA.interior_eq
  -- `interior A ⊆ interior (closure A)` by monotonicity of `interior`
  have h_sub : A ⊆ interior (closure A) := by
    have hIntSubset : interior A ⊆ interior (closure A) :=
      interior_mono subset_closure
    simpa [h_int_eq] using hIntSubset
  -- Apply the inclusion to the given point `x`
  have hx_int : x ∈ interior (closure A) := h_sub hxA
  -- Rewrite `interior (closure (interior A))` using `h_int_eq`
  simpa [h_int_eq] using hx_int

theorem interior_closure_eq_interior_closure_interior_of_P2 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have h : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 hP2
  simpa [h]

theorem interior_closure_interior_eq_interior_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply subset_antisymm
  · -- `interior (closure (interior A)) ⊆ interior A`
    have h_closure_subset : closure (interior A) ⊆ A := by
      have h_int_subset : interior A ⊆ A := interior_subset
      have h' : closure (interior A) ⊆ closure A := closure_mono h_int_subset
      simpa [hA.closure_eq] using h'
    exact interior_mono h_closure_subset
  · -- `interior A ⊆ interior (closure (interior A))`
    have h_subset : interior A ⊆ closure (interior A) := by
      intro x hx
      exact subset_closure hx
    have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono h_subset
    simpa [interior_interior] using h'

theorem isOpen_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  have h_subset : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure
  exact h_subset hx_int

theorem interior_closure_inter_subset_inter_interior_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure (A ∩ B)` is contained in each of `closure A` and `closure B`
  have hA : closure (A ∩ B) ⊆ closure A := closure_mono Set.inter_subset_left
  have hB : closure (A ∩ B) ⊆ closure B := closure_mono Set.inter_subset_right
  -- Taking interiors preserves these inclusions
  have hA_int : interior (closure (A ∩ B)) ⊆ interior (closure A) := interior_mono hA
  have hB_int : interior (closure (A ∩ B)) ⊆ interior (closure B) := interior_mono hB
  -- Apply the inclusions to the given point `x`
  have hxA : x ∈ interior (closure A) := hA_int hx
  have hxB : x ∈ interior (closure B) := hB_int hx
  exact And.intro hxA hxB

theorem union_interior_closure_subset_interior_closure_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  rcases hx with hxA | hxB
  · -- Case: `x ∈ interior (closure A)`
    have hA : closure A ⊆ closure (A ∪ B) :=
      closure_mono (Set.subset_union_left)
    have hA_int : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
      interior_mono hA
    exact hA_int hxA
  · -- Case: `x ∈ interior (closure B)`
    have hB : closure B ⊆ closure (A ∪ B) :=
      closure_mono (Set.subset_union_right)
    have hB_int : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
      interior_mono hB
    exact hB_int hxB

theorem interior_closure_eq_interior_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  have h : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [h]

theorem isOpen_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hxA
  -- Rewrite `interior A` using the openness of `A`
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  -- Any point of `interior A` lies in `closure (interior A)`
  exact subset_closure hx_int

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  exact interior_mono (closure_interior_mono hAB)

theorem closed_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) (hP1 : Topology.P1 A) :
    A = closure (interior A) := by
  have h : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [hA.closure_eq] using h

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  -- `interior A` is contained in `closure (interior A)`
  have h_sub : interior A ⊆ closure (interior A) := by
    intro y hy
    exact subset_closure hy
  -- Taking interiors preserves the inclusion
  have h_mono : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h_sub
  -- Rewrite `interior (interior A)` and apply the inclusion to `x`
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  exact h_mono hx'

theorem isOpen_union_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P2 (A ∪ B) := by
  -- The union of two open sets is open
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  -- Apply the existing result for open sets
  exact Topology.isOpen_P2 (A := A ∪ B) hOpen

theorem closure_interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  exact closure_interior_mono (A := A) (B := closure A) subset_closure

theorem interior_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (interior_closure_interior_eq_interior_of_closed
      (X := X) (A := closure A) hClosed)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  rcases hx with hxA | hxB
  · -- Case: x ∈ A
    have hx_closure : x ∈ closure (interior A) := hA hxA
    have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
      have h_int_subset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact closure_mono h_int_subset
    exact h_subset hx_closure
  · -- Case: x ∈ B
    have hx_closure : x ∈ closure (interior B) := hB hxB
    have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
      have h_int_subset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact closure_mono h_int_subset
    exact h_subset hx_closure

theorem interior_closure_eq_interior_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA.closure_eq]

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure (interior A)) := hA hxA
      have h_subset : interior (closure (interior A))
          ⊆ interior (closure (interior (A ∪ B))) := by
        have h_int_subset : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        have h_closure_subset :
            closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure (interior B)) := hB hxB
      have h_subset : interior (closure (interior B))
          ⊆ interior (closure (interior (A ∪ B))) := by
        have h_int_subset : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        have h_closure_subset :
            closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hx'

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact h_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact h_subset hxB'

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_P2 (A := interior (closure A)) hOpen

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_P1 (A := interior (closure A)) hOpen

theorem P1_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_P1 (A := interior (closure (interior A))) hOpen

theorem dense_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hxA
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    have h : interior ((Set.univ : Set X)) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure] using h
  have hx_univ : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int] using hx_univ

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_P3 (A := interior (closure A)) hOpen

theorem P2_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_P2 (A := interior (closure (interior A))) hOpen

theorem P3_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    -- First, show `A ⊆ interior A`
    have h_sub : A ⊆ interior A := by
      intro x hx
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    -- We always have `interior A ⊆ A`
    have h_sub' : interior A ⊆ A := interior_subset
    -- Hence `A = interior A`
    have h_eq : interior A = A := subset_antisymm h_sub' h_sub
    -- `interior A` is open, so `A` is open
    have h_open_int : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using h_open_int
  · intro hOpen
    exact Topology.isOpen_P3 hOpen

theorem interior_closure_interior_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx_closure : x ∈ closure (interior A) := interior_subset hx
  have h_sub : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (A := A)
  exact h_sub hx_closure

theorem P3_closed_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A → Topology.P2 A := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P2]
  intro x hxA
  -- From `P3`, `x` lies in `interior (closure A)`, but since `A` is closed,
  -- this is just `interior A`.
  have hx_intA : x ∈ interior A := by
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hA.closure_eq] using this
  -- `interior A` is contained in `interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) :=
    interior_subset_interior_closure_interior
  exact h_subset hx_intA

theorem closure_eq_closure_interior_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : closure A = closure (interior A) := by
  simpa [hA.interior_eq]

theorem P1_closed_iff_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  have h_cl : closure A = A := hA.closure_eq
  have h_equiv := Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  simpa [h_cl, eq_comm] using h_equiv

theorem interior_closure_interior_closure_interior_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (interior_closure_interior_eq_interior_of_closed
      (X := X) (A := closure (interior A)) hClosed)

theorem interior_closure_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_imp_P3 (A := A) hP2
  · intro hP3
    exact (Topology.P3_closed_imp_P2 (A := A) hA) hP3

theorem closure_interior_closure_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure A))) = closure (interior (closure A)) := by
  simpa [closure_closure]

theorem P2_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  have h1 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_closed (A := A) hA
  have h2 : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  simpa using h1.trans h2

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact Topology.isOpen_P2 (A := A) hA
  · intro _hP2
    exact Topology.isOpen_P1 (A := A) hA

theorem interior_closure_interior_closure_subset_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) ⊆ interior (closure A) := by
  -- First note: `interior (closure A)` is contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  have h₂' : closure (interior (closure A)) ⊆ closure A := by
    simpa [closure_closure] using h₂
  -- Taking interiors preserves inclusions, giving the desired result.
  exact interior_mono h₂'

theorem isOpen_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    And.intro
      (Topology.isOpen_P1 (A := A) hA)
      (And.intro
        (Topology.isOpen_P2 (A := A) hA)
        (Topology.isOpen_P3 (A := A) hA))

theorem P2_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P3]
  intro x hxA
  -- `x` belongs to the closure of `A`
  have hx_closure : x ∈ closure A := subset_closure hxA
  -- Apply `P2` for `closure A`
  have hx_int₁ : x ∈ interior (closure (interior (closure A))) := hP2 hx_closure
  -- Relate the two interiors of closures
  have h_subset :
      interior (closure (interior (closure A))) ⊆ interior (closure A) := by
    have h₁ :
        interior (closure (interior (closure A))) ⊆
          interior (closure (closure A)) :=
      interior_closure_interior_subset_interior_closure (X := X) (A := closure A)
    simpa [closure_closure] using h₁
  -- Conclude that `x` is in `interior (closure A)`
  exact h_subset hx_int₁

theorem P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- For an open set, `interior A = A`.
  have h_int : interior A = A := hA.interior_eq
  -- Rewrite `P2` using the above equality.
  have hP2 : Topology.P2 A ↔ A ⊆ interior (closure A) := by
    dsimp [Topology.P2]
    simpa [h_int]
  -- `P3` is already exactly the same inclusion.
  have h : (A ⊆ interior (closure A)) ↔ Topology.P3 A := by
    dsimp [Topology.P3]
    exact Iff.rfl
  -- Combine the two equivalences.
  exact hP2.trans h

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  cases hx

theorem interior_closure_interior_subset_interior_closure_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  -- The set `A` is always contained in its closure.
  have hA : (A : Set X) ⊆ closure A := subset_closure
  -- Apply monotonicity of `interior ∘ closure ∘ interior`.
  exact
    Topology.interior_closure_interior_mono
      (X := X) (A := A) (B := closure A) hA

theorem P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h1 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h2 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  exact h1.trans h2

theorem closure_interior_inter_subset_inter_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
  have hA : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono (interior_mono Set.inter_subset_left)
  have hB : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono (interior_mono Set.inter_subset_right)
  exact And.intro (hA hx) (hB hx)

theorem interior_closure_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- The closure of a set contains the set itself.
  exact subset_closure hx

theorem interior_closure_interior_eq_interior_closure_of_open {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    interior (closure (interior A)) = interior (closure A) := by
  simpa [hA.interior_eq]

theorem closure_interior_closure_interior_closure_interior_eq {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior (closure (interior A))) := by
  have h :=
    interior_closure_interior_closure_interior_eq
      (X := X) (A := A)
  simpa [h]

theorem dense_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P2 (closure A) := by
  intro hDense
  dsimp [Topology.P2]
  intro x hx_cl
  -- `closure A` is closed.
  have hClosed : IsClosed (closure A) := isClosed_closure
  -- For a closed set, `interior (closure (interior C)) = interior C`.
  have h_int_eq :
      interior (closure (interior (closure A))) = interior (closure A) :=
    interior_closure_interior_eq_interior_of_closed
      (X := X) (A := closure A) hClosed
  -- Since `A` is dense, `closure A = univ`.
  have h_closure_univ : (closure A : Set X) = Set.univ := hDense.closure_eq
  -- Hence `interior (closure A) = univ`.
  have h_int_univ : interior (closure A) = (Set.univ : Set X) := by
    have : interior (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure_univ] using this
  -- Combining the two equalities, the target interior is `univ`.
  have h_target :
      interior (closure (interior (closure A))) = (Set.univ : Set X) := by
    simpa [h_int_univ] using h_int_eq
  -- Any point belongs to `univ`, so we are done.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_target] using this

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx

theorem P3_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_P3 (A := interior (closure (interior A))) hOpen

theorem dense_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P1 (closure A) := by
  intro hDense
  dsimp [Topology.P1]
  intro x _hx
  -- Since `A` is dense, `closure A = univ`.
  have h_closure_univ : (closure A : Set X) = Set.univ := hDense.closure_eq
  -- Hence `interior (closure A) = univ`.
  have h_int_eq : interior (closure A) = (Set.univ : Set X) := by
    have h_univ : interior (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure_univ] using h_univ
  -- Therefore `closure (interior (closure A)) = univ`.
  have h_target_eq : closure (interior (closure A)) = (Set.univ : Set X) := by
    have h_closure_univ' : closure (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using closure_univ
    simpa [h_int_eq] using h_closure_univ'
  -- Conclude the desired membership.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_target_eq] using this

theorem P2_iff_P3_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure A) ↔ Topology.P3 (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P2_iff_P3_of_closed (A := closure A) hClosed)

theorem dense_imp_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (closure A) := by
  intro hDense
  have hP2 : Topology.P2 (closure A) :=
    dense_imp_P2_closure (A := A) hDense
  exact Topology.P2_imp_P3 (A := closure A) hP2

theorem interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using
            (interior_closure_interior_closure_interior_eq
              (X := X) (A := closure A))
    _ = interior (closure A) := by
          simpa using
            (interior_closure_interior_closure_eq
              (X := X) (A := A))

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx



theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  -- `Set.univ` is open, hence it satisfies `P1` by `isOpen_P1`.
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  exact Topology.isOpen_P1 (A := Set.univ) hOpen

theorem closure_interior_union_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `interior A ⊆ interior (A ∪ B)` by monotonicity of `interior`.
      have h_int_subset :
          interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion.
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hA
  | inr hB =>
      -- Symmetric case for `B`.
      have h_int_subset :
          interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hB

theorem P2_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using
    (Topology.P2_iff_P3_of_isOpen (A := interior A) hOpen)

theorem interior_closure_interior_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`.
  have hA : interior (A ∩ B) ⊆ interior A :=
    interior_mono Set.inter_subset_left
  have hB : interior (A ∩ B) ⊆ interior B :=
    interior_mono Set.inter_subset_right
  -- Taking closures preserves these inclusions.
  have hA_closure : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono hA
  have hB_closure : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono hB
  -- Taking interiors again preserves the inclusions.
  have hA_int :
      interior (closure (interior (A ∩ B))) ⊆ interior (closure (interior A)) :=
    interior_mono hA_closure
  have hB_int :
      interior (closure (interior (A ∩ B))) ⊆ interior (closure (interior B)) :=
    interior_mono hB_closure
  -- Apply the inclusions to the given point `x`.
  exact And.intro (hA_int hx) (hB_int hx)

theorem interior_subset_closure_set {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hx
  exact subset_closure (interior_subset hx)

theorem P2_interior_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior (closure A)))) := by
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact Topology.isOpen_P2 (A := interior (closure (interior (closure A)))) hOpen

theorem P3_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P3 (interior (closure (interior (closure A)))) := by
  -- The set in question is open, since it is an interior.
  have hOpen : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_P3 (A := interior (closure (interior (closure A)))) hOpen

theorem P3_closed_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  -- From `P3` and closedness, deduce that `A` is open.
  have hOpen : IsOpen A :=
    ((Topology.P3_closed_iff_isOpen (A := A) hA).1) hP3
  -- Any open set satisfies `P1`.
  exact Topology.isOpen_P1 (A := A) hOpen

theorem P3_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3Closure
  dsimp [Topology.P3] at hP3Closure
  dsimp [Topology.P3]
  intro x hxA
  -- A point of `A` is in `closure A`.
  have hx_closure : x ∈ closure A := subset_closure hxA
  -- Apply `P3` for `closure A`.
  have hx_int : x ∈ interior (closure (closure A)) := hP3Closure hx_closure
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using hx_int

theorem closure_eq_closure_interior_of_P3_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    Topology.P3 A → closure A = closure (interior A) := by
  intro hP3
  have hP2 : Topology.P2 A := (Topology.P3_closed_imp_P2 (A := A) hA) hP3
  exact Topology.closure_eq_closure_interior_of_P2 (A := A) hP2

theorem P2_closed_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  -- From closedness, `P2` is equivalent to `P3`.
  have hP3 : Topology.P3 A :=
    ((Topology.P2_iff_P3_of_closed (A := A) hA).1) hP2
  -- A closed set satisfying `P3` also satisfies `P1`.
  exact (Topology.P3_closed_imp_P1 (A := A) hA) hP3

theorem interior_closure_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) ⊆ closure A := by
  intro x hx
  exact interior_subset hx

theorem interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]



theorem interior_closure_interior_subset_closure_inter_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure A ∩ interior (closure A) := by
  intro x hx
  have h_cl : x ∈ closure A :=
    interior_closure_interior_subset_closure (X := X) (A := A) hx
  have h_int : x ∈ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A) hx
  exact And.intro h_cl h_int

theorem P1_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using
    (Topology.P1_iff_P3_of_isOpen (A := interior A) hOpen)

theorem interior_closure_interior_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (interior (Set.univ : Set X))) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]

theorem closure_interior_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem P1_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  dsimp [Topology.P1]
  intro x hx
  -- First, upgrade `x ∈ closure A` to `x ∈ closure (interior A)`.
  have h₁ : closure A ⊆ closure (interior A) := by
    have h := closure_mono hP1
    simpa [closure_closure] using h
  have hx₁ : x ∈ closure (interior A) := h₁ hx
  -- Next, use monotonicity to land in `closure (interior (closure A))`.
  have h₂ :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (X := X) (A := A)
  exact h₂ hx₁

theorem closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  -- First, identify the key equality for interiors using the closedness of `closure A`.
  have hInt :
      interior (closure (interior (closure A))) = interior (closure A) := by
    have hClosed : IsClosed (closure A) := isClosed_closure
    simpa using
      (interior_closure_interior_eq_interior_of_closed
        (X := X) (A := closure A) hClosed)
  -- Taking closures of both sides preserves equality.
  simpa [hInt]

theorem P1_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen (A := interior A) hOpen)

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure A := by
  -- The interior of `A` is contained in `A`.
  have h : interior A ⊆ A := interior_subset
  -- Monotonicity of `closure` turns this into the desired inclusion.
  exact closure_mono h

theorem interior_eq_empty_of_closure_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (∅ : Set X) → interior A = (∅ : Set X) := by
  intro h
  ext x
  constructor
  · intro hx
    have : x ∈ closure (interior A) := subset_closure hx
    simpa [h] using this
  · intro hx
    cases hx

theorem closure_interior_eq_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAopen : IsOpen A) (hAclosed : IsClosed A) :
    closure (interior A) = A := by
  have hInt : interior A = A := hAopen.interior_eq
  have hCl : closure A = A := hAclosed.closure_eq
  calc
    closure (interior A) = closure A := by
      simpa [hInt]
    _ = A := hCl

theorem interior_closure_eq_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAopen : IsOpen A) (hAclosed : IsClosed A) :
    interior (closure A) = A := by
  -- Since `A` is closed, its closure equals itself.
  have hClosure : closure A = A := hAclosed.closure_eq
  -- Since `A` is open, its interior equals itself.
  have hInterior : interior A = A := hAopen.interior_eq
  -- Combine the two equalities to reach the goal.
  calc
    interior (closure A) = interior A := by
      simpa [hClosure]
    _ = A := by
      simpa [hInterior]

theorem interior_closure_eq_of_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : closure A = closure B) :
    interior (closure A) = interior (closure B) := by
  simpa [h]

theorem interior_subset_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ⊆ closure (interior A) := by
  intro x hx
  exact subset_closure hx

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → interior (closure A) = (Set.univ : Set X) := by
  intro hDense
  have h_closure : (closure A : Set X) = Set.univ := hDense.closure_eq
  simpa [h_closure, interior_univ]

theorem union_interior_closure_interior_subset_interior_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A ⊆ interior (A ∪ B)` by monotonicity of `interior`.
      have h_int_subset :
          interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion.
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      -- Taking interiors again preserves the inclusion.
      have h_int_closure_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      exact h_int_closure_subset hxA
  | inr hxB =>
      -- Symmetric case for `B`.
      have h_int_subset :
          interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      have h_int_closure_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      exact h_int_closure_subset hxB

theorem closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure A)) ⊆ closure A := by
  have h : interior (closure A) ⊆ closure A := interior_subset
  simpa [closure_closure] using (closure_mono h)

theorem closure_interior_closure_interior_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₁ : interior A ⊆ interior (closure (interior A)) :=
      interior_subset_interior_closure_interior (X := X) (A := A)
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂

theorem closure_interior_closure_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (closure (Set.univ : Set X))) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is contained in `interior (closure (interior A))`
  have hInt :
      interior A ⊆ interior (closure (interior A)) :=
    interior_subset_interior_closure_interior (X := X) (A := A)
  -- Taking closures preserves this inclusion
  have hClosure :
      closure (interior A) ⊆
        closure (interior (closure (interior A))) :=
    closure_mono hInt
  exact hClosure hx

theorem P1_closure_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (interior A)))) := by
  -- First, `interior (closure (interior A))` satisfies `P1`
  have hP1_inner : Topology.P1 (interior (closure (interior A))) :=
    P1_interior_closure_interior (X := X) (A := A)
  -- Taking the closure of a set that satisfies `P1` yields another set satisfying `P1`
  exact P1_imp_P1_closure (A := interior (closure (interior A))) hP1_inner

theorem closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → closure (interior (closure A)) = (Set.univ : Set X) := by
  intro hDense
  -- `closure A = univ` because `A` is dense.
  have h_closure_univ : (closure A : Set X) = Set.univ := hDense.closure_eq
  -- Hence `interior (closure A) = univ`.
  have h_int_univ : interior (closure A) = (Set.univ : Set X) := by
    have h_univ : interior (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure_univ] using h_univ
  -- Taking closures preserves the equality, so the target closure is also `univ`.
  calc
    closure (interior (closure A))
        = closure (Set.univ : Set X) := by
          simpa [h_int_univ]
    _ = (Set.univ : Set X) := by
          simpa using closure_univ

theorem closure_interior_inter_subset_closure_inter_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A ∩ interior B) := by
  -- The interior of `A ∩ B` is contained in both `interior A` and `interior B`.
  have h :
      interior (A ∩ B) ⊆ interior A ∩ interior B := by
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono Set.inter_subset_left) hx
    have hxB : x ∈ interior B :=
      (interior_mono Set.inter_subset_right) hx
    exact And.intro hxA hxB
  -- Taking closures preserves inclusions.
  exact closure_mono h

theorem interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  simpa using
    (interior_closure_interior_closure_interior_closure_eq
      (X := X) (A := interior A))

theorem closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  have h12 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h23 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  constructor
  · intro hP1
    have hP2 : Topology.P2 A := (h12.mp hP1)
    have hP3 : Topology.P3 A := (h23.mp hP2)
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    exact (h12.mpr hP2)

theorem closure_interior_subset_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h₁ : interior A ⊆ A := interior_subset
  have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
  simpa [hA.closure_eq] using h₂

theorem closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure A)))))) =
      closure (interior (closure A)) := by
  calc
    closure (interior (closure (interior (closure (interior (closure A)))))) =
        closure (interior (closure (interior (closure A)))) := by
          simpa using
            (closure_interior_closure_interior_closure_interior_eq
              (X := X) (A := closure A))
    _ = closure (interior (closure A)) := by
          simpa using
            (closure_interior_closure_interior_eq
              (X := X) (A := closure A))

theorem closure_unionInterior_subset_closure_interiorUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  -- First, show that `interior A ∪ interior B ⊆ interior (A ∪ B)`.
  have h_sub : (interior A ∪ interior B : Set X) ⊆ interior (A ∪ B) := by
    intro y hy
    cases hy with
    | inl hA =>
        -- Points of `interior A` are certainly in `interior (A ∪ B)`.
        have : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact this hA
    | inr hB =>
        -- Symmetric argument for `interior B`.
        have : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact this hB
  -- Taking closures preserves inclusions.
  exact fun x hx => (closure_mono h_sub) hx

theorem closure_interior_union_eq_union_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  simpa using (closure_union (s := interior A) (t := interior B))

theorem interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  -- First, simplify the innermost three alternating applications.
  have h1 :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure A) := by
    simpa using
      (interior_closure_interior_closure_interior_closure_eq
        (X := X) (A := A))
  -- Use `h1` to rewrite the larger expression.
  have h2 :
      interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure (interior (closure A))) := by
    simpa [h1]
  -- Finally, collapse the remaining two alternating applications.
  simpa
    [interior_closure_interior_closure_eq (X := X) (A := A)]
    using h2

theorem interior_closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → interior (closure (interior (closure A))) = (Set.univ : Set X) := by
  intro hDense
  -- First, use the existing result about the closure being all of `univ`.
  have h_closure :
      closure (interior (closure A)) = (Set.univ : Set X) :=
    closure_interior_closure_eq_univ_of_dense (X := X) (A := A) hDense
  -- Taking interiors on both sides yields the desired equality.
  calc
    interior (closure (interior (closure A)))
        = interior (Set.univ : Set X) := by
          simpa [h_closure]
    _ = (Set.univ : Set X) := by
          simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq

theorem P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure A))) := by
  -- First, `interior (closure A)` satisfies `P1`.
  have hInner : Topology.P1 (interior (closure A)) :=
    P1_interior_closure (X := X) (A := A)
  -- Taking the closure of a set that satisfies `P1` yields another set satisfying `P1`.
  exact P1_imp_P1_closure (A := interior (closure A)) hInner

theorem dense_imp_P1_P2_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → (Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A)) := by
  intro hDense
  have hP1 : Topology.P1 (closure A) := dense_imp_P1_closure (A := A) hDense
  have hP2 : Topology.P2 (closure A) := dense_imp_P2_closure (A := A) hDense
  have hP3 : Topology.P3 (closure A) := dense_imp_P3_closure (A := A) hDense
  exact And.intro hP1 (And.intro hP2 hP3)

theorem interior_closure_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simp [closure_empty]

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, apply monotonicity of `closure` to the inclusion `A ⊆ B`.
  have h_closure : closure A ⊆ closure B := closure_mono hAB
  -- Next, use monotonicity of `interior` to relate the interiors.
  have h_interior : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure
  -- Finally, another application of `closure_mono` yields the desired inclusion.
  exact closure_mono h_interior

theorem interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (interior (closure A))))))))
      ) = interior (closure A) := by
  -- Step 1: use the previously established four-step idempotence
  have h4 :
      interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure A) :=
    interior_closure_interior_closure_interior_closure_interior_closure_eq
      (X := X) (A := A)
  -- Step 2: apply `interior ∘ closure` to both sides of `h4`
  have h5 :
      interior (closure (interior (closure (interior (closure (interior (closure (interior (closure A))))))))
        ) = interior (closure (interior (closure A))) :=
    congrArg (fun S : Set X => interior (closure S)) h4
  -- Step 3: finish with the two-step idempotence lemma
  calc
    interior (closure (interior (closure (interior (closure (interior (closure (interior (closure A))))))))
      ) = interior (closure (interior (closure A))) := by
        simpa using h5
    _ = interior (closure A) := by
        simpa using interior_closure_interior_closure_eq (X := X) (A := A)

theorem P2_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_imp_P1 (A := A) hP2
  exact Topology.P1_imp_P1_closure (A := A) hP1

theorem P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_isOpen (A := closure A) hClosed)

theorem closed_eq_closure_interior_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A → A = closure (interior A) := by
  intro hP3
  have h := Topology.closure_eq_closure_interior_of_P3_closed (A := A) hA hP3
  simpa [hA.closure_eq] using h

theorem closed_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A → A = closure (interior A) := by
  intro hP2
  -- From `P2`, we get equality of the two closures.
  have h := Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using h

theorem interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hxIntA
  -- Step 1: `x` lies in `interior (closure A)` because interiors are monotone
  have hxIntClosureA : x ∈ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A) hxIntA
  -- Step 2: every point of `interior (closure A)` lies in
  --         `closure (interior (closure A))`
  have hIncl : interior (closure A) ⊆ closure (interior (closure A)) := by
    intro y hy
    exact subset_closure hy
  -- Finish by combining the two facts
  exact hIncl hxIntClosureA

theorem closure_interior_inter_eq_closure_interior_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ interior B) = closure (interior (A ∩ B)) := by
  simpa [interior_inter]

theorem P3_closure_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P2 (closure A) := by
  intro hP3
  exact ((Topology.P2_iff_P3_closure (A := A)).mpr hP3)

theorem P1_P2_P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) ∧
      Topology.P2 (interior (closure A)) ∧
        Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_imp_P1_P2_P3 (A := interior (closure A)) hOpen

theorem isClosed_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (closure A))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (closure A))))

theorem closure_interior_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simpa [interior_empty] using (closure_empty : closure (∅ : Set X) = ∅)

theorem isOpen_interior_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    IsOpen (interior (closure (interior A))) := by
  simpa using
    (isOpen_interior :
      IsOpen (interior (closure (interior A))))

theorem isClosed_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior A)) := by
  simpa using (isClosed_closure : IsClosed (closure (interior A)))

theorem closure_interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- Step 1: the basic two-step idempotence.
  have h₁ :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (closure_interior_closure_interior_eq
        (X := X) (A := A))
  -- Step 2: apply `closure ∘ interior` to both sides of `h₁`.
  have h₂ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      congrArg (fun S : Set X => closure (interior S)) h₁
  -- Step 3: simplify the right-hand side with `h₁`.
  simpa [h₁] using h₂

theorem P3_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_isOpen (A := closure (interior A)) hClosed)

theorem P1_closure_iff_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure A) ↔ closure A = closure (interior (closure A)) := by
  -- Apply the general equivalence to the set `closure A`,
  -- then simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := closure A))

theorem closure_inter_subset_inter_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : closure (A ∩ B) ⊆ closure A := closure_mono Set.inter_subset_left
  have hB : closure (A ∩ B) ⊆ closure B := closure_mono Set.inter_subset_right
  exact And.intro (hA hx) (hB hx)

theorem P2_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  -- `closure (interior A)` is always a closed set.
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  -- Apply the general equivalence for closed sets.
  simpa using
    (Topology.P2_closed_iff_isOpen (A := closure (interior A)) hClosed)

theorem closure_union_closed_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed B) :
    closure (A ∪ B) = closure A ∪ B := by
  have h := closure_union (s := A) (t := B)
  simpa [hB.closure_eq] using h

theorem closure_closure_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem closure_interior_eq_empty_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (∅ : Set X) → closure (interior A) = (∅ : Set X) := by
  intro h
  simpa [h, closure_empty]



theorem closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `closure (A ∩ interior B)` is contained in `closure A`
  have hxA : x ∈ closure A := by
    have h₁ : A ∩ interior B ⊆ A := Set.inter_subset_left
    have h₂ : closure (A ∩ interior B) ⊆ closure A := closure_mono h₁
    exact h₂ hx
  -- `closure (A ∩ interior B)` is contained in `closure B`
  have hxB : x ∈ closure B := by
    -- First, note that `A ∩ interior B ⊆ B`
    have h₁ : A ∩ interior B ⊆ B := by
      intro y hy
      exact interior_subset hy.2
    -- Taking closures preserves the inclusion
    have h₂ : closure (A ∩ interior B) ⊆ closure B := closure_mono h₁
    exact h₂ hx
  exact And.intro hxA hxB

theorem closure_interior_union_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∪ interior (closure A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl h₁ =>
      exact closure_interior_subset_closure (X := X) (A := A) h₁
  | inr h₂ =>
      exact interior_closure_subset_closure (X := X) (A := A) h₂

theorem closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∩ interior (closure A) = interior (closure A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact And.intro
      ((interior_subset : interior (closure A) ⊆ closure A) hx)
      hx

theorem union_interior_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h hA
  | inr hB =>
      have h : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact h hB

theorem closure_union_interior_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ∪ interior B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `closure A` is contained in `closure (A ∪ B)` by monotonicity of `closure`.
      have h : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h hxA
  | inr hxB =>
      -- `interior B` is contained in `B`.
      have hxB_in_B : x ∈ B := interior_subset hxB
      -- Hence `x` belongs to `A ∪ B`.
      have hx_union : x ∈ A ∪ B := Or.inr hxB_in_B
      -- Any point of `A ∪ B` lies in its closure.
      exact subset_closure hx_union

theorem interior_interior_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior (closure A)) = interior (closure A) := by
  simpa [interior_interior]

theorem dense_interior_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P1 A := by
  intro hDense
  dsimp [Topology.P1]
  intro x hxA
  -- Since `interior A` is dense, its closure is `univ`.
  have h_closure : (closure (interior A) : Set X) = Set.univ := hDense.closure_eq
  -- Every point lies in `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure] using hx_univ

theorem isOpen_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  have hP1A : Topology.P1 A :=
    Topology.isOpen_P1 (A := A) hA
  exact Topology.P1_imp_P1_closure (A := A) hP1A

theorem interior_closure_inter_interior_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure (A ∩ interior B)` is contained in `closure A`
  have hA : closure (A ∩ interior B) ⊆ closure A :=
    closure_mono Set.inter_subset_left
  -- `closure (A ∩ interior B)` is contained in `closure B`
  have hB : closure (A ∩ interior B) ⊆ closure B := by
    -- First, note that `A ∩ interior B ⊆ B`
    have h : A ∩ interior B ⊆ B := by
      intro y hy
      exact interior_subset hy.2
    -- Taking closures preserves the inclusion
    exact closure_mono h
  -- Taking interiors preserves these inclusions
  have hA_int : interior (closure (A ∩ interior B)) ⊆ interior (closure A) :=
    interior_mono hA
  have hB_int : interior (closure (A ∩ interior B)) ⊆ interior (closure B) :=
    interior_mono hB
  -- Apply the inclusions to the given point `x`
  have hxA : x ∈ interior (closure A) := hA_int hx
  have hxB : x ∈ interior (closure B) := hB_int hx
  exact And.intro hxA hxB

theorem interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (Aᶜ) = (closure A)ᶜ := by
  simpa using interior_compl (s := A)

theorem closure_interior_closure_eq_closure_of_open {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  apply subset_antisymm
  ·
    exact closure_interior_closure_subset_closure (X := X) (A := A)
  ·
    -- Since `A` is open, we have `A ⊆ interior (closure A)`.
    have h_sub : (A : Set X) ⊆ interior (closure A) := by
      have hIntSubset : interior A ⊆ interior (closure A) :=
        interior_mono subset_closure
      simpa [hA.interior_eq] using hIntSubset
    -- Taking closures preserves inclusions.
    exact closure_mono h_sub

theorem interior_closure_union_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A ∪ interior A)) = interior (closure A) := by
  -- First, show that `A ∪ interior A = A`.
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA => exact hA
      | inr hIntA => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  -- Rewrite using the established equality.
  simpa [h_union]

theorem dense_closed_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsClosed A → A = (Set.univ : Set X) := by
  intro hDense hClosed
  have h : (closure A : Set X) = Set.univ := hDense.closure_eq
  simpa [hClosed.closure_eq] using h

theorem closure_interior_inter_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior A) ∩ closure A = closure (interior A) := by
  ext x
  constructor
  · intro h
    exact h.1
  · intro hx
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_interior_subset_closure (X := X) (A := A)
    exact And.intro hx (h_subset hx)

theorem interior_closure_interclosure_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure A ∩ closure B` is contained in each of its factors.
  have hSubA : closure A ∩ closure B ⊆ closure A := by
    intro y hy
    exact hy.1
  have hSubB : closure A ∩ closure B ⊆ closure B := by
    intro y hy
    exact hy.2
  -- Taking interiors preserves these inclusions.
  have hIntA : interior (closure A ∩ closure B) ⊆ interior (closure A) :=
    interior_mono hSubA
  have hIntB : interior (closure A ∩ closure B) ⊆ interior (closure B) :=
    interior_mono hSubB
  -- Apply the inclusions to the given point `x`.
  exact And.intro (hIntA hx) (hIntB hx)

theorem interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ closure A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    have hxCl : x ∈ closure A := subset_closure hxA
    exact And.intro hxInt hxCl

theorem P3_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P1]
  intro x hx_closureA
  -- From `P3`, we have `A ⊆ interior (closure A)`.
  have hA_in : (A : Set X) ⊆ interior (closure A) := by
    dsimp [Topology.P3] at hP3
    exact hP3
  -- Taking closures preserves inclusions.
  have h_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hA_in
  exact h_subset hx_closureA

theorem P1_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 (A ∪ interior B) := by
  intro hP1A
  -- `interior B` automatically satisfies `P1`.
  have hP1IntB : Topology.P1 (interior B) :=
    Topology.P1_interior (X := X) (A := B)
  -- Combine the two `P1` sets using the existing union lemma.
  exact
    (Topology.P1_union (A := A) (B := interior B) hP1A hP1IntB)

theorem dense_interior_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 A := by
  intro hDense
  dsimp [Topology.P2]
  intro x hxA
  -- Since `interior A` is dense, its closure is `univ`.
  have h_closure : (closure (interior A) : Set X) = Set.univ := hDense.closure_eq
  -- Hence the interior of this closure is also `univ`.
  have h_int : interior (closure (interior A)) = (Set.univ : Set X) := by
    have h_univ : interior (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure] using h_univ
  -- Every point lies in `univ`, so the desired inclusion holds.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int] using this

theorem interior_subset_closure_of_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} (h : B ⊆ closure A) :
    interior B ⊆ closure A := by
  intro x hx
  have hxB : x ∈ B := interior_subset hx
  exact h hxB

theorem interior_closure_diff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  intro x hx
  -- `A \ B` is contained in `A`.
  have h_sub : (A \ B : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  -- Taking closures and then interiors preserves inclusions.
  have h_incl :
      interior (closure (A \ B)) ⊆ interior (closure A) :=
    interior_mono (closure_mono h_sub)
  exact h_incl hx

theorem interior_closure_subset_interior_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ⊆ interior (closure (A ∪ B)) := by
  exact
    interior_mono
      (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))

theorem closure_interior_union_interior_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A ∪ interior A)) = closure (interior A) := by
  -- Since `interior A ⊆ A`, we have `A ∪ interior A = A`.
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA => exact hA
      | inr hIntA => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  simpa [h_union]

theorem interior_diff_subset_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  -- `A \ B` is contained in `A`.
  have h_sub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `interior` gives the desired inclusion.
  exact interior_mono h_sub

theorem interior_closure_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- Show the two sets are equal by extensionality.
    ext x
    constructor
    · intro _hx
      -- Any point in `closure A` is trivially in `univ`.
      trivial
    · intro _hx
      -- Since `interior (closure A) = univ`, every point of `univ` lies in
      -- `interior (closure A)`, and hence in `closure A`.
      have : x ∈ interior (closure A) := by
        simpa [hInt] using (by
          -- `x` is an arbitrary point of `univ`.
          trivial : x ∈ (Set.univ : Set X))
      exact interior_subset this
  · intro hCl
    -- Rewrite the left‐hand side using `hCl` and simplify.
    simpa [hCl, interior_univ]

theorem interior_closure_union_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A ∪ closure B) = interior (closure (A ∪ B)) := by
  simpa [closure_union]

theorem closure_inter_interior_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ interior A = interior A := by
  simpa [Set.inter_comm]
    using interior_inter_closure_eq_interior (X := X) (A := A)

theorem P1_P2_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  simpa using
    (Topology.isOpen_imp_P1_P2_P3 (A := (∅ : Set X)) isOpen_empty)

theorem isClosed_iff_closure_interior_eq_of_open {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    IsClosed A ↔ closure (interior A) = A := by
  have hInt : interior A = A := hA.interior_eq
  constructor
  · intro hClosed
    calc
      closure (interior A)
          = closure A := by
            simpa [hInt]
      _ = A := hClosed.closure_eq
  · intro hEq
    -- From the given equality and `hInt`, deduce `closure A = A`.
    have hCl : closure A = A := by
      simpa [hInt] using hEq
    -- `closure A` is always closed; rewrite using `hCl`.
    have hClosedClosure : IsClosed (closure A) := isClosed_closure
    simpa [hCl] using hClosedClosure

theorem closure_union_interior_closure_eq_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∪ interior (closure A) = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl h₁ => exact h₁
    | inr h₂ =>
        exact (interior_subset : interior (closure A) ⊆ closure A) h₂
  · intro x hx
    exact Or.inl hx

theorem closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (Aᶜ) = (interior A)ᶜ := by
  -- Apply `interior_compl_eq_compl_closure` to `Aᶜ`:
  have h : interior A = (closure (Aᶜ))ᶜ := by
    have h' := interior_compl_eq_compl_closure (X := X) (A := Aᶜ)
    simpa [compl_compl] using h'
  -- Complement both sides of `h` to obtain the desired equality.
  have h' : (interior A)ᶜ = closure (Aᶜ) := by
    simpa using congrArg Set.compl h
  simpa using h'.symm

theorem dense_interior_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hxA
  -- The closure of `interior A` is the whole space.
  have hClosureInt : (closure (interior A) : Set X) = Set.univ := hDense.closure_eq
  -- Hence `closure A` must also be the whole space.
  have hSubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hUnivSub : (Set.univ : Set X) ⊆ closure A := by
    simpa [hClosureInt] using hSubset
  have hClosureA : (closure A : Set X) = Set.univ := by
    apply subset_antisymm
    · exact Set.subset_univ _
    · exact hUnivSub
  -- Therefore `interior (closure A)` is also the whole space.
  have hIntClosureA : interior (closure A) = (Set.univ : Set X) :=
    (interior_closure_eq_univ_iff (A := A)).2 hClosureA
  -- Conclude the desired membership.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hIntClosureA] using this

theorem P1_imp_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior (closure A)) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  intro x hxA
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  have h_subset : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (A := A)
  exact h_subset hx_cl

theorem interior_inter_closure_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ closure (Aᶜ) = (∅ : Set X) := by
  -- `closure (Aᶜ)` is the complement of `interior A`.
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (X := X) (A := A)
  -- Rewrite and simplify the intersection.
  simpa [h, Set.inter_compl_self]

theorem compl_interior_compl_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    (interior (Aᶜ))ᶜ = closure A := by
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [compl_compl] using congrArg Set.compl h

theorem P1_P2_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧
      Topology.P2 (interior A) ∧
        Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_imp_P1_P2_P3 (A := interior A) hOpen

theorem isOpen_iff_interior_closure_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    IsOpen A ↔ interior (closure A) = A := by
  have hCl : closure A = A := hA.closure_eq
  constructor
  · intro hOpen
    calc
      interior (closure A) = interior A := by
        simpa [hCl]
      _ = A := by
        simpa [hOpen.interior_eq]
  · intro hEq
    -- From the given equality and `hCl`, deduce `interior A = A`.
    have hIntA : interior A = A := by
      simpa [hCl] using hEq
    -- `interior A` is open; rewrite using `hIntA`.
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hIntA] using hOpenInt

theorem interior_closure_compl_eq_compl_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (Aᶜ)) = (closure (interior A))ᶜ := by
  -- First, express `closure (Aᶜ)` as the complement of `interior A`.
  have h₁ : (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (X := X) (A := A)
  -- Take interiors of both sides and rewrite using `interior_compl`.
  calc
    interior (closure (Aᶜ))
        = interior ((interior A)ᶜ) := by
          simpa [h₁]
    _ = (closure (interior A))ᶜ := by
          simpa using
            (interior_compl (s := interior A))

theorem interior_inter_closure_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `A ∩ closure B` is contained in `closure A`
  have hSubA : (A ∩ closure B : Set X) ⊆ closure A := by
    intro y hy
    exact subset_closure hy.1
  -- `A ∩ closure B` is also contained in `closure B`
  have hSubB : (A ∩ closure B : Set X) ⊆ closure B := by
    intro y hy
    exact hy.2
  -- Taking interiors preserves these inclusions
  have hxA : x ∈ interior (closure A) := (interior_mono hSubA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono hSubB) hx
  exact And.intro hxA hxB



theorem interior_subset_closure_interior_closure_fixed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hxIntA
  -- First, use the monotonicity of `interior` to lift the point to
  -- `interior (closure A)`.
  have hxIntClA : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxIntA
  -- Any point of an interior lies in the closure of that interior.
  exact subset_closure hxIntClA

theorem interior_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hIntA, hIntAc⟩
    -- From the two interior memberships, derive membership in `A ∩ Aᶜ`,
    -- which is empty.
    have hAAc : x ∈ (A ∩ Aᶜ) := by
      exact And.intro (interior_subset hIntA) (interior_subset hIntAc)
    simpa [Set.inter_compl_self] using hAAc
  · exact Set.empty_subset _

theorem closure_union_closure_compl_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro _x hx
    trivial
  · intro x _
    by_cases hA : x ∈ A
    · exact Or.inl (subset_closure hA)
    · have hAc : x ∈ Aᶜ := by
        simpa using hA
      exact Or.inr (subset_closure hAc)

theorem inter_subset_closure_left_right {X : Type*} [TopologicalSpace X]
    {U V A B : Set X} (hU : U ⊆ closure A) (hV : V ⊆ closure B) :
    (U ∩ V : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  exact And.intro (hU hx.1) (hV hx.2)

theorem closure_interior_closure_interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  -- Use the previously established eight-step idempotence.
  have h :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior A) :=
    closure_interior_closure_interior_closure_interior_closure_interior_eq
      (X := X) (A := A)
  -- Apply `closure ∘ interior` to both sides of `h`.
  simpa using congrArg (fun S : Set X => closure (interior S)) h

theorem interior_eq_empty_of_interior_closure_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure A) = (∅ : Set X) → interior A = (∅ : Set X) := by
  intro h
  ext x
  constructor
  · intro hx
    have hx' : x ∈ interior (closure A) := by
      have h_subset : interior A ⊆ interior (closure A) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      exact h_subset hx
    simpa [h] using hx'
  · intro hx
    cases hx

theorem isOpen_interior.compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed ((interior A)ᶜ) := by
  simpa using (isOpen_interior : IsOpen (interior A)).isClosed_compl

theorem closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  -- First, rewrite `interior (Aᶜ)` using the standard complement formula.
  have h₁ : interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  -- Substitute the rewrite into the goal and apply the corresponding
  -- formula for the closure of a complement.
  calc
    closure (interior (Aᶜ)) = closure ((closure A)ᶜ) := by
      simpa [h₁]
    _ = (interior (closure A))ᶜ := by
      simpa using
        (closure_compl_eq_compl_interior (A := closure A))

theorem closure_eq_closure_interior_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → closure A = closure (interior (closure A)) := by
  intro hP1
  -- Step 1: use `P1` to relate `closure A` and `closure (interior A)`.
  have h₁ : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Step 2: obtain an equality for the two corresponding interiors.
  have h₂ :
      interior (closure A) = interior (closure (interior A)) :=
    interior_closure_eq_interior_closure_interior_of_P1 (A := A) hP1
  -- Step 3: apply `closure` to both sides of `h₂`.
  have h₃ :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) := by
    simpa using congrArg (fun s : Set X => closure s) h₂
  -- Step 4: simplify the right‐hand side using the idempotence lemma.
  have h₄ :
      closure (interior (closure (interior A))) = closure (interior A) :=
    closure_interior_closure_interior_eq (X := X) (A := A)
  -- Step 5: chain the equalities together.
  calc
    closure A
        = closure (interior A) := h₁
    _ = closure (interior (closure (interior A))) := (h₄.symm)
    _ = closure (interior (closure A)) := by
        simpa using h₃.symm

theorem interior_eq_compl_closure_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A = (closure (Aᶜ))ᶜ := by
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  calc
    interior A = ((interior A)ᶜ)ᶜ := by
      simp
    _ = (closure (Aᶜ))ᶜ := by
      simpa [h]

theorem interior_closure_inter_interior_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure (interior B)) := by
  intro x hx
  -- `closure (A ∩ interior B)` is contained in `closure A`
  have hA : closure (A ∩ interior B) ⊆ closure A :=
    closure_mono Set.inter_subset_left
  -- `closure (A ∩ interior B)` is also contained in `closure (interior B)`
  have hB : closure (A ∩ interior B) ⊆ closure (interior B) := by
    have hSub : (A ∩ interior B : Set X) ⊆ interior B := by
      intro y hy
      exact hy.2
    exact closure_mono hSub
  -- Taking interiors preserves these inclusions
  have hxA : x ∈ interior (closure A) := (interior_mono hA) hx
  have hxB : x ∈ interior (closure (interior B)) := (interior_mono hB) hx
  exact And.intro hxA hxB

theorem closure_compl_eq_self_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    closure (Aᶜ) = Aᶜ := by
  have hClosed : IsClosed (Aᶜ) := hA.isClosed_compl
  simpa using hClosed.closure_eq

theorem closure_inter_closure_compl_eq_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ closure (Aᶜ) = frontier A := by
  -- First, rewrite `closure (Aᶜ)` using a standard complement formula.
  have h : (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  -- Prove the desired equality by set extensionality.
  ext x
  constructor
  · intro hx
    -- `hx` gives `x ∈ closure A` and `x ∈ closure (Aᶜ)`.
    have hx₁ : x ∈ closure A := hx.1
    have hx₂ : x ∈ (interior A)ᶜ := by
      -- Replace `closure (Aᶜ)` with `(interior A)ᶜ` using `h`.
      simpa [h] using hx.2
    -- Combine the two facts to obtain membership in `frontier A`.
    exact And.intro hx₁ hx₂
  · intro hx
    -- `hx` gives `x ∈ closure A` and `x ∈ (interior A)ᶜ`.
    have hx₁ : x ∈ closure A := hx.1
    have hx₂ : x ∈ closure (Aᶜ) := by
      -- Replace `(interior A)ᶜ` with `closure (Aᶜ)` using `h`.
      simpa [h] using hx.2
    -- Combine the two facts to obtain membership in the intersection.
    exact And.intro hx₁ hx₂

theorem closure_inter_interior_eq_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A ∩ interior A) = closure (interior A) := by
  apply subset_antisymm
  · -- `A ∩ interior A` is contained in `interior A`
    have h₁ : (A ∩ interior A : Set X) ⊆ interior A := by
      intro x hx
      exact hx.2
    -- Taking closures preserves inclusions
    exact closure_mono h₁
  · -- `interior A` is contained in `A ∩ interior A`
    have h₂ : (interior A : Set X) ⊆ A ∩ interior A := by
      intro x hx
      exact And.intro (interior_subset hx) hx
    -- Taking closures preserves inclusions
    exact closure_mono h₂

theorem interior_subset_inter_self_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ⊆ A ∩ interior (closure A) := by
  intro x hxIntA
  -- `x` lies in `A` because it lies in `interior A`.
  have hxA : x ∈ A := interior_subset hxIntA
  -- `x` also lies in `interior (closure A)` by monotonicity of `interior`.
  have hxIntClA : x ∈ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A) hxIntA
  exact And.intro hxA hxIntClA



theorem frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier A = closure A \ interior A := by
  -- Begin with the characterization of the frontier as an intersection
  have h₁ : closure A ∩ closure (Aᶜ) = frontier A := by
    simpa using
      (closure_inter_closure_compl_eq_frontier (X := X) (A := A))
  -- Express the set difference as an intersection with a complement
  have h₂ : closure A \ interior A = closure A ∩ (interior A)ᶜ := rfl
  -- Relate `closure (Aᶜ)` to the complement of `interior A`
  have h₃ : (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  -- Rewrite the frontier using `h₃`
  have h₄ : frontier A = closure A ∩ (interior A)ᶜ := by
    simpa [h₃] using h₁.symm
  -- Conclude by substituting the two intermediate identities
  simpa [h₂] using h₄

theorem interior_closure_inter_subset_interior_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A ∩ closure B) := by
  -- First, show the underlying inclusion for the closed sets themselves.
  have h_subset : closure (A ∩ B) ⊆ closure A ∩ closure B := by
    intro x hx
    have hxA : x ∈ closure A :=
      (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
    have hxB : x ∈ closure B :=
      (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    exact And.intro hxA hxB
  -- Taking interiors preserves inclusions.
  exact interior_mono h_subset

theorem P2_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 (A ∪ interior B) := by
  intro hP2A
  have hP2IntB : Topology.P2 (interior B) :=
    Topology.P2_interior (X := X) (A := B)
  have h := Topology.P2_union (A := A) (B := interior B) hP2A hP2IntB
  simpa using h

theorem closure_interior_union_interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∪ interior (closure A) ⊆
      closure (interior (closure A)) := by
  intro x hx
  cases hx with
  | inl hx₁ =>
      -- `closure (interior A)` is contained in `closure (interior (closure A))`
      have h :=
        closure_interior_subset_closure_interior_closure
          (X := X) (A := A) hx₁
      exact h
  | inr hx₂ =>
      -- `interior (closure A)` is evidently contained in its own closure
      have h_sub :
          interior (closure A) ⊆ closure (interior (closure A)) := by
        intro y hy
        exact subset_closure hy
      exact h_sub hx₂

theorem interior_union_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A ∪ closure A) = interior (closure A) := by
  -- First, observe that `A ∪ closure A` coincides with `closure A`.
  have h_union : (A ∪ closure A : Set X) = closure A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA   => exact subset_closure hA
      | inr hClA => exact hClA
    · intro hx
      exact Or.inr hx
  -- Rewrite the goal using the equality just established.
  simpa [h_union]

theorem frontier_eq_closure_diff_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    frontier A = closure A \ A := by
  have h := frontier_eq_closure_diff_interior (X := X) (A := A)
  simpa [hA.interior_eq] using h

theorem interior_inter_of_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  ext x
  constructor
  · intro hx
    have hAB : x ∈ A ∩ B := interior_subset hx
    have hxA : x ∈ A := hAB.1
    have hxIntB : x ∈ interior B := by
      have hSub : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact (interior_mono hSub) hx
    exact And.intro hxA hxIntB
  · rintro ⟨hxA, hxIntB⟩
    -- Consider the open set `A ∩ interior B` containing `x`.
    have hOpen : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    have hMem₁ : x ∈ (A ∩ interior B) := And.intro hxA hxIntB
    -- This open set is contained in `A ∩ B`.
    have hSub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact And.intro hy.1 (interior_subset hy.2)
    -- Hence `A ∩ B` belongs to the neighbourhoods of `x`.
    have hMem₂ : (A ∩ B : Set X) ∈ nhds x :=
      Filter.mem_of_superset (hOpen.mem_nhds hMem₁) hSub
    -- Conclude that `x` is in the interior of `A ∩ B`.
    exact (mem_interior_iff_mem_nhds).2 hMem₂

theorem closure_union_interior_compl_eq_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∪ interior (Aᶜ) = (Set.univ : Set X) := by
  have h : interior (Aᶜ : Set X) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  calc
    closure A ∪ interior (Aᶜ) = closure A ∪ (closure A)ᶜ := by
      simpa [h]
    _ = (Set.univ : Set X) := Set.union_compl_self (closure A)

theorem interior_union_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ closure (interior A) = closure (interior A) := by
  -- We first note that `interior A` is contained in `closure (interior A)`.
  have h_sub : (interior A : Set X) ⊆ closure (interior A) := by
    intro x hx
    exact subset_closure hx
  -- Now we establish the desired set equality.
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hx_int => exact h_sub hx_int
    | inr hx_cl  => exact hx_cl
  · intro x hx
    exact Or.inr hx

theorem interior_closure_interior_subset_closure_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆
      closure (interior A) ∩ interior (closure A) := by
  intro x hx
  have hx_closure : x ∈ closure (interior A) := interior_subset hx
  have hx_interior : x ∈ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A) hx
  exact And.intro hx_closure hx_interior

theorem interior_union_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = A ∪ B := by
  simpa using (hA.union hB).interior_eq

theorem interior_inter_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ interior (closure A) = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    -- `interior A` is contained in `interior (closure A)` by monotonicity.
    have h_subset : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    have hx_int_cl : x ∈ interior (closure A) := h_subset hx
    exact And.intro hx hx_int_cl

theorem interior_inter_of_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  ext x
  constructor
  · intro hx
    have hAB : x ∈ A ∩ B := interior_subset hx
    have hxB : x ∈ B := hAB.2
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    have hxIntA : x ∈ interior A := (interior_mono hSub) hx
    exact And.intro hxIntA hxB
  · rintro ⟨hxIntA, hxB⟩
    -- Consider the open set `interior A ∩ B` containing `x`.
    have hOpen : IsOpen (interior A ∩ B) := isOpen_interior.inter hB
    have hxMem : x ∈ interior A ∩ B := And.intro hxIntA hxB
    -- This open set is contained in `A ∩ B`.
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy; exact And.intro (interior_subset hy.1) hy.2
    -- Hence `A ∩ B` belongs to the neighbourhoods of `x`.
    have hNhd : (A ∩ B : Set X) ∈ nhds x :=
      Filter.mem_of_superset (hOpen.mem_nhds hxMem) hSub
    -- Conclude that `x` is in the interior of `A ∩ B`.
    exact (mem_interior_iff_mem_nhds).2 hNhd

theorem closure_interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure A)) := by
  have h :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure
      (X := X) (A := A)
  exact closure_mono h

theorem frontier_eq_diff_interior_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    frontier A = A \ interior A := by
  have h := frontier_eq_closure_diff_interior (X := X) (A := A)
  simpa [hA.closure_eq] using h

theorem interior_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  simpa using (hA.inter hB).interior_eq

theorem interior_inter_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ (Aᶜ) = (∅ : Set X) := by
  -- First, observe that `interior A` is contained in `A`.
  have h_subset : interior A ⊆ (A : Set X) := interior_subset
  -- Establish the two inclusions needed for set equality.
  apply Set.Subset.antisymm
  · -- `interior A ∩ Aᶜ ⊆ ∅`
    intro x hx
    -- `x` lies in both `interior A` and `Aᶜ`.
    have hA : x ∈ A := h_subset hx.1
    have hAc : x ∈ Aᶜ := hx.2
    -- Contradiction.
    exact (hAc hA).elim
  · -- `∅ ⊆ interior A ∩ Aᶜ`
    exact Set.empty_subset _

theorem interior_closure_interior_inter_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ∩ interior (closure A) =
      interior (closure (interior A)) := by
  apply (Set.inter_eq_left).2
  exact
    Topology.interior_closure_interior_subset_interior_closure
      (X := X) (A := A)



theorem interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A :=
    (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hxB : x ∈ interior B :=
    (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact And.intro hxA hxB

theorem closure_interior_inter_eq_closure_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- `A` and `B` are open, hence so is their intersection.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- For an open set, the interior equals the set itself.
  have hInt : interior (A ∩ B) = A ∩ B := hOpen.interior_eq
  -- Substitute this identity into the goal.
  simpa [hInt]



theorem interior_closure_interInterior_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A ∩ interior B)) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- `interior A ∩ interior B` is contained in `interior A`
  have hSubA : (interior A ∩ interior B : Set X) ⊆ interior A := by
    intro y hy
    exact hy.1
  -- and also contained in `interior B`
  have hSubB : (interior A ∩ interior B : Set X) ⊆ interior B := by
    intro y hy
    exact hy.2
  -- Taking closures preserves these inclusions
  have hClA :
      closure (interior A ∩ interior B) ⊆ closure (interior A) :=
    closure_mono hSubA
  have hClB :
      closure (interior A ∩ interior B) ⊆ closure (interior B) :=
    closure_mono hSubB
  -- Taking interiors again preserves the inclusions
  have hIntA :
      interior (closure (interior A ∩ interior B)) ⊆
        interior (closure (interior A)) :=
    interior_mono hClA
  have hIntB :
      interior (closure (interior A ∩ interior B)) ⊆
        interior (closure (interior B)) :=
    interior_mono hClB
  -- Apply the inclusions to the given point `x`
  exact And.intro (hIntA hx) (hIntB hx)

theorem interior_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior A ⊆ interior (closure B) := by
  -- First, upgrade the inclusion `A ⊆ B` to `A ⊆ closure B`.
  have h₁ : (A : Set X) ⊆ closure B := by
    intro x hx
    have : x ∈ B := hAB hx
    exact subset_closure this
  -- Monotonicity of `interior` yields the desired result.
  exact interior_mono h₁

theorem closure_union_interior_eq_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ B) = closure (interior A) ∪ closure B := by
  simpa using (closure_union (s := interior A) (t := B))

theorem interior_subset_of_subset_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hB : IsOpen B) :
    interior A ⊆ B := by
  intro x hxIntA
  exact hAB (interior_subset hxIntA)

theorem P1_iff_P1_closure_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P1 A ↔ Topology.P1 (closure A) := by
  have h_cl : closure A = A := hA.closure_eq
  constructor
  · intro hP1
    exact P1_imp_P1_closure (A := A) hP1
  · intro hP1_cl
    simpa [h_cl] using hP1_cl

theorem closure_union_closed_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) :
    closure (A ∪ B) = A ∪ closure B := by
  have h := closure_union (s := A) (t := B)
  simpa [hA.closure_eq] using h

theorem interior_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  calc
    interior A ∪ closure (Aᶜ)
        = interior A ∪ (interior A)ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := Set.union_compl_self (interior A)

theorem interior_subset_interior_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ⊆ interior (A ∪ B) := by
  exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)

theorem P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h1 : Topology.P2 (closure A) ↔ Topology.P3 (closure A) :=
    Topology.P2_iff_P3_closure (A := A)
  have h2 : Topology.P3 (closure A) ↔ IsOpen (closure A) :=
    Topology.P3_closure_iff_isOpen_closure (A := A)
  exact h1.trans h2

theorem P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  -- For closed sets, `P3` is equivalent to being open.
  have h₁ : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  -- A set is open iff its interior equals itself.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa [hOpen.interior_eq]
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  simpa using h₁.trans h₂

theorem Set.compl_compl {α : Type*} {s : Set α} : ((sᶜ)ᶜ : Set α) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem union_closure_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    (A ∪ closure A : Set X) = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hA   => exact subset_closure hA
    | inr hClA => exact hClA
  · intro x hx
    exact Or.inr hx

theorem closure_eq_union_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A = A ∪ frontier A := by
  ext x
  constructor
  · intro hx
    by_cases hA : x ∈ A
    · exact Or.inl hA
    · -- `x` is not in `A`, so it must lie in the frontier.
      have h_not_int : x ∉ interior A := by
        intro hxInt
        exact hA (interior_subset hxInt)
      have h_front : x ∈ frontier A := And.intro hx h_not_int
      exact Or.inr h_front
  · intro h
    cases h with
    | inl hA =>
        exact subset_closure hA
    | inr hFront =>
        exact hFront.1

theorem compl_frontier_eq_compl_closure_union_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    (frontier A)ᶜ = (closure A)ᶜ ∪ interior A := by
  -- First, rewrite the frontier as an intersection.
  have h₁ : (frontier A : Set X) = closure A ∩ (interior A)ᶜ := by
    have h := frontier_eq_closure_diff_interior (X := X) (A := A)
    simpa [Set.diff_eq] using h
  -- Take complements of both sides.
  have h₂ : (frontier A)ᶜ = (closure A ∩ (interior A)ᶜ)ᶜ := by
    simpa [h₁]
  -- Use De Morgan's laws to simplify the right-hand side.
  simpa [Set.compl_inter, Set.compl_compl] using h₂

theorem interior_closure_interior_eq_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAopen : IsOpen A) (hAclosed : IsClosed A) :
    interior (closure (interior A)) = A := by
  have hInt : interior A = A := hAopen.interior_eq
  calc
    interior (closure (interior A))
        = interior (closure A) := by
          simpa [hInt]
    _ = A := by
          simpa using
            interior_closure_eq_of_clopen (A := A) hAopen hAclosed

theorem frontier_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier A ⊆ closure A := by
  intro x hx
  -- By definition, `x ∈ frontier A` means `x ∈ closure A` and `x ∉ interior A`.
  exact hx.1

theorem frontier_subset_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    frontier A ⊆ A := by
  intro x hx
  -- From `hx` we have `x ∈ closure A`.
  have hx_closure : x ∈ closure A := hx.1
  -- For a closed set, its closure is itself.
  simpa [hA.closure_eq] using hx_closure

theorem frontier_compl_eq_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (Aᶜ) = frontier A := by
  -- First, rewrite both frontiers using the `closure \ interior` characterisation.
  have h₁ :
      frontier (Aᶜ) = closure (Aᶜ) \ interior (Aᶜ) := by
    simpa using
      (frontier_eq_closure_diff_interior (X := X) (A := Aᶜ))
  have h₂ :
      frontier A = closure A \ interior A := by
    simpa using
      (frontier_eq_closure_diff_interior (X := X) (A := A))
  -- Next, express `closure (Aᶜ)` and `interior (Aᶜ)` in terms of `A`.
  have h_cl :
      (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  have h_int :
      interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  -- Substitute these identities into `h₁`.
  have h₁' :
      frontier (Aᶜ) = (interior A)ᶜ \ (closure A)ᶜ := by
    simpa [h_cl, h_int] using h₁
  -- Re-express the set difference as an intersection with a complement.
  have h₁'' :
      frontier (Aᶜ) = closure A ∩ (interior A)ᶜ := by
    simpa [Set.diff_eq, Set.compl_compl, Set.inter_comm, Set.inter_left_comm]
      using h₁'
  -- Do the same for `h₂`.
  have h₂' :
      frontier A = closure A ∩ (interior A)ᶜ := by
    simpa [Set.diff_eq] using h₂
  -- Conclude by transitivity.
  simpa [h₂'] using h₁''

theorem eq_empty_of_P2_and_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (∅ : Set X) → Topology.P2 A → A = (∅ : Set X) := by
  intro hInt hP2
  -- `P2` gives an inclusion of `A` into an interior of a closure.
  have h_sub : (A : Set X) ⊆ interior (closure (interior A)) := hP2
  -- Simplify the target interior using the assumption `interior A = ∅`.
  have h_empty : interior (closure (interior A)) = (∅ : Set X) := by
    simpa [hInt, closure_empty, interior_empty]
  -- From the two facts we get `A ⊆ ∅`.
  have h_subset_empty : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    have : x ∈ interior (closure (interior A)) := h_sub hx
    simpa [h_empty] using this
  -- Conclude the desired equality by extensionality.
  apply subset_antisymm h_subset_empty (Set.empty_subset _)

theorem frontier_subset_closure_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ⊆ closure (Aᶜ) := by
  intro x hx
  -- Reinterpret `hx` using the characterization
  -- `frontier A = closure A ∩ closure (Aᶜ)`.
  have hx_inter : x ∈ closure A ∩ closure (Aᶜ) := by
    have h_eq :=
      (closure_inter_closure_compl_eq_frontier (X := X) (A := A)).symm
    simpa [h_eq] using hx
  -- Conclude with the second component of the intersection.
  exact hx_inter.2

theorem frontier_subset_compl_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ⊆ (interior A)ᶜ := by
  intro x hx
  exact hx.2

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  have h₁ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_closed (A := A) hA
  have h₂ : Topology.P3 A ↔ interior A = A :=
    Topology.P3_closed_iff_interior_eq (A := A) hA
  exact h₁.trans h₂

theorem interior_union_closure_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ closure A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hInt =>
        -- `x` lies in `interior A`, hence in `A`, hence in `closure A`.
        exact
          (subset_closure (interior_subset hInt))
    | inr hCl =>
        exact hCl
  · intro x hx
    -- Any point of `closure A` is in the right component of the union.
    exact Or.inr hx

theorem closure_eq_closureInterior_union_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A = closure (interior A) ∪ frontier A := by
  ext x
  constructor
  · intro hx
    by_cases hInt : x ∈ interior A
    · -- `x` is an interior point of `A`
      have hx' : x ∈ closure (interior A) := subset_closure hInt
      exact Or.inl hx'
    · -- `x` is not an interior point of `A`, hence it lies in the frontier
      have hFront : x ∈ frontier A := by
        -- `frontier A = closure A \ interior A`
        have : x ∈ closure A ∧ x ∉ interior A := And.intro hx hInt
        simpa [frontier, Set.diff_eq] using this
      exact Or.inr hFront
  · intro h
    cases h with
    | inl hClInt =>
        -- `closure (interior A)` is contained in `closure A`
        have hSub : closure (interior A) ⊆ closure A :=
          closure_interior_subset_closure (A := A)
        exact hSub hClInt
    | inr hFront =>
        -- Points of the frontier belong to `closure A`
        exact hFront.1

theorem P3_union_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → IsOpen B → Topology.P3 (A ∪ B) := by
  intro hP3A hOpenB
  have hP3B : Topology.P3 B := Topology.isOpen_P3 (A := B) hOpenB
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B

theorem frontier_isClosed {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (frontier A) := by
  -- Express `frontier A` as an intersection of two closed sets.
  have h_eq : (frontier A : Set X) = closure A ∩ closure (Aᶜ) := by
    simpa using
      (closure_inter_closure_compl_eq_frontier (X := X) (A := A)).symm
  -- The intersection of two closed sets is closed.
  have h_closed : IsClosed (closure A ∩ closure (Aᶜ)) := by
    have h₁ : IsClosed (closure A) := isClosed_closure
    have h₂ : IsClosed (closure (Aᶜ)) := isClosed_closure
    exact h₁.inter h₂
  simpa [h_eq] using h_closed

theorem closure_diff_subset_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A \ A ⊆ frontier A := by
  rintro x ⟨hx_cl, hx_notA⟩
  have hx_notInt : x ∉ interior A := by
    intro hx_int
    exact hx_notA (interior_subset hx_int)
  exact And.intro hx_cl hx_notInt

theorem P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalences for open sets
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  constructor
  · intro hP3
    -- From `P3` obtain `P2`, then `P1`
    have hP2 : Topology.P2 A := (h₂.symm).mp hP3
    have hP1 : Topology.P1 A := (h₁.mpr) hP2
    exact And.intro hP1 hP2
  · rintro ⟨hP1, hP2⟩
    -- From `P2` obtain `P3`
    exact (h₂.mp) hP2

theorem closure_eq_closure_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  -- First, `P3 A` yields `P1 (closure A)`.
  have hP1 : Topology.P1 (closure A) :=
    Topology.P3_imp_P1_closure (A := A) hP3
  -- Apply the `P1` result to `closure A`.
  have hEq : closure (closure A) = closure (interior (closure A)) :=
    Topology.closure_eq_closure_interior_of_P1 (A := closure A) hP1
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using hEq

theorem closure_frontier_eq_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier A) = frontier A := by
  have hClosed : IsClosed (frontier A) := frontier_isClosed (X := X) (A := A)
  simpa using hClosed.closure_eq

theorem frontier_closure_subset_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure A) ⊆ frontier A := by
  intro x hx
  -- `hx` gives `x ∈ closure (closure A)` and `x ∉ interior (closure A)`.
  have hx_closureA : x ∈ closure A := by
    simpa [closure_closure] using hx.1
  -- Show that `x` is not in `interior A`.
  have hx_not_intA : x ∉ interior A := by
    intro hx_intA
    -- Since `interior A ⊆ interior (closure A)`, this contradicts `hx.2`.
    have : x ∈ interior (closure A) := by
      have h_subset : interior A ⊆ interior (closure A) :=
        interior_subset_interior_closure
      exact h_subset hx_intA
    exact hx.2 this
  exact And.intro hx_closureA hx_not_intA

theorem frontier_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- Unpack the definition of `frontier`.
  rcases hx with ⟨hx_cl_union, hx_not_int_union⟩
  -- A point in `closure (A ∪ B)` lies in `closure A ∪ closure B`.
  have h_cl : x ∈ closure A ∪ closure B := by
    simpa [closure_union] using hx_cl_union
  -- Split on the two possibilities.
  cases h_cl with
  | inl hx_clA =>
      -- Show `x` is *not* in `interior A`.
      have hx_not_intA : x ∉ interior A := by
        intro hx_intA
        have : x ∈ interior (A ∪ B) := by
          have h_sub : interior A ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
          exact h_sub hx_intA
        exact hx_not_int_union this
      -- Conclude `x ∈ frontier A`.
      exact Or.inl ⟨hx_clA, hx_not_intA⟩
  | inr hx_clB =>
      -- Symmetric argument for `B`.
      have hx_not_intB : x ∉ interior B := by
        intro hx_intB
        have : x ∈ interior (A ∪ B) := by
          have h_sub : interior B ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
          exact h_sub hx_intB
        exact hx_not_int_union this
      exact Or.inr ⟨hx_clB, hx_not_intB⟩

theorem frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) ⊆ frontier A := by
  intro x hx
  -- Unpack the definition of membership in the frontier of `interior A`.
  rcases hx with ⟨hx_cl_int, hx_not_int_int⟩
  -- `interior A ⊆ A`, so taking closures yields the corresponding inclusion.
  have hx_closureA : x ∈ closure A := by
    have h_subset : (interior A : Set X) ⊆ A := interior_subset
    exact (closure_mono h_subset) hx_cl_int
  -- `x` is not in `interior (interior A) = interior A`.
  have hx_not_intA : x ∉ interior A := by
    simpa [interior_interior] using hx_not_int_int
  -- Combine the facts to conclude `x ∈ frontier A`.
  exact And.intro hx_closureA hx_not_intA

theorem frontier_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    frontier (∅ : Set X) = (∅ : Set X) := by
  simpa [frontier_eq_closure_diff_interior]



theorem interior_inter_closure_of_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ closure B) = A ∩ interior (closure B) := by
  simpa using
    (interior_inter_of_isOpen_left (X := X) (A := A) (B := closure B) hA)

theorem frontier_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_notInt⟩
  -- `x` lies in the closure of each factor.
  have h_clA : x ∈ closure A := by
    have h : closure (A ∩ B) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact h hx_cl
  have h_clB : x ∈ closure B := by
    have h : closure (A ∩ B) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact h hx_cl
  -- Case distinction on whether `x` is in `interior A`.
  by_cases hIntA : x ∈ interior A
  · -- If `x ∈ interior A`, show `x ∉ interior B`.
    have h_notIntB : x ∉ interior B := by
      intro hIntB
      -- Both `A` and `B` are neighbourhoods of `x`.
      have hA_nhds : (A : Set X) ∈ nhds x :=
        (mem_interior_iff_mem_nhds).1 hIntA
      have hB_nhds : (B : Set X) ∈ nhds x :=
        (mem_interior_iff_mem_nhds).1 hIntB
      -- Their intersection is also a neighbourhood of `x`.
      have hAB_nhds : (A ∩ B : Set X) ∈ nhds x :=
        Filter.inter_mem hA_nhds hB_nhds
      -- Hence `x ∈ interior (A ∩ B)`, contradicting `hx_notInt`.
      have : x ∈ interior (A ∩ B) :=
        (mem_interior_iff_mem_nhds).2 hAB_nhds
      exact hx_notInt this
    -- Therefore `x ∈ frontier B`.
    exact Or.inr ⟨h_clB, h_notIntB⟩
  · -- Otherwise `x ∉ interior A`, so `x ∈ frontier A`.
    exact Or.inl ⟨h_clA, hIntA⟩

theorem frontier_eq_self_of_closed_of_empty_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hInt : interior A = (∅ : Set X)) :
    frontier A = A := by
  have h := frontier_eq_diff_interior_of_closed (X := X) (A := A) hA_closed
  simpa [hInt] using h

theorem frontier_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) ⊆ closure A := by
  intro x hx
  -- Unpack the definition of `frontier (interior A)`.
  rcases hx with ⟨hx_cl, _hx_not_int⟩
  -- `closure (interior A)` is contained in `closure A` because `interior A ⊆ A`.
  have h_sub : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact h_sub hx_cl

theorem frontier_interior_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior (closure A)) ⊆ frontier A := by
  intro x hx
  -- Unpack `hx` into the two conditions defining the frontier.
  have hx_cl  : x ∈ closure (interior (closure A)) := hx.1
  have hx_nint : x ∉ interior (interior (closure A)) := hx.2
  -- `closure (interior (closure A))` is contained in `closure A`.
  have h_sub_cl : closure (interior (closure A)) ⊆ closure A :=
    closure_interior_closure_subset_closure (X := X) (A := A)
  have hx_clA : x ∈ closure A := h_sub_cl hx_cl
  -- Show that `x` is not in `interior A`.
  have hx_nintA : x ∉ interior A := by
    intro hx_intA
    -- `interior A ⊆ interior (closure A)`.
    have h_sub_int : (interior A : Set X) ⊆ interior (closure A) :=
      interior_subset_interior_closure (A := A)
    have hx_int_clA : x ∈ interior (closure A) := h_sub_int hx_intA
    -- Rewrite `interior (closure A)` as `interior (interior (closure A))`.
    have : x ∈ interior (interior (closure A)) := by
      simpa [interior_interior] using hx_int_clA
    exact hx_nint this
  -- Conclude that `x` lies in the frontier of `A`.
  exact And.intro hx_clA hx_nintA

theorem frontier_frontier_subset_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (frontier A) ⊆ frontier A := by
  intro x hx
  -- `hx` provides `x ∈ closure (frontier A)`.
  have h_cl : x ∈ closure (frontier A) := hx.1
  -- Since `frontier A` is closed, its closure is itself.
  have h_closed : closure (frontier A) = frontier A := by
    have hIsClosed : IsClosed (frontier A) := frontier_isClosed (X := X) (A := A)
    simpa using hIsClosed.closure_eq
  -- Rewrite using the equality and finish.
  simpa [h_closed] using h_cl

theorem frontier_inter_interior_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ∩ interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hFront : x ∈ frontier A := hx.1
    have hInt   : x ∈ interior A := hx.2
    have hNotInt : x ∉ interior A :=
      (frontier_subset_compl_interior (X := X) (A := A)) hFront
    have : False := hNotInt hInt
    simpa using this
  · intro x hx
    cases hx

theorem frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    frontier (A : Set X) ⊆ closure B := by
  intro x hx
  -- `hx` gives `x ∈ closure A`
  have hx_closureA : x ∈ closure A := hx.1
  -- Monotonicity of `closure` upgrades the inclusion
  have h_mono : closure A ⊆ closure B := closure_mono hAB
  exact h_mono hx_closureA

theorem frontier_closure_eq_closure_diff_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure A) = closure A \ interior (closure A) := by
  simpa [frontier_eq_closure_diff_interior, closure_closure]

theorem closure_frontier_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier A) ⊆ closure A := by
  -- `frontier A` is closed, hence its closure equals itself.
  have h_eq : closure (frontier A) = frontier A := by
    have hClosed : IsClosed (frontier A) := frontier_isClosed (X := X) (A := A)
    simpa using hClosed.closure_eq
  -- The frontier of `A` is contained in `closure A`.
  have h_subset : frontier A ⊆ closure A :=
    frontier_subset_closure (X := X) (A := A)
  simpa [h_eq] using h_subset

theorem interior_inter_interior_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (interior A ∩ interior B) = interior A ∩ interior B := by
  -- `interior A` and `interior B` are open, hence so is their intersection.
  have hOpen : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  -- For an open set, the interior equals the set itself.
  simpa [hOpen.interior_eq]

theorem frontier_eq_empty_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAopen : IsOpen A) (hAclosed : IsClosed A) :
    frontier A = (∅ : Set X) := by
  have hInt : interior A = A := hAopen.interior_eq
  have hClos : closure A = A := hAclosed.closure_eq
  calc
    frontier A = closure A \ interior A := by
      simpa using frontier_eq_closure_diff_interior (X := X) (A := A)
    _ = A \ interior A := by
      simpa [hClos]
    _ = A \ A := by
      simpa [hInt]
    _ = (∅ : Set X) := by
      simp

theorem frontier_closure_eq_frontier_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    frontier (closure A) = frontier A := by
  simpa [hA.closure_eq]

theorem closure_interior_union_closure_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∪ closure A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl h₁ =>
        have h_subset : closure (interior A) ⊆ closure A :=
          closure_interior_subset_closure (X := X) (A := A)
        exact h_subset h₁
    | inr h₂ =>
        exact h₂
  · intro x hx
    exact Or.inr hx

theorem dense_frontier_eq_compl_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → frontier (A : Set X) = (Set.univ : Set X) \ interior A := by
  intro hDense
  -- For a dense set, its closure is the whole space.
  have h_closure : (closure A : Set X) = Set.univ := hDense.closure_eq
  -- Rewrite the frontier via the standard characterization.
  have h_frontier : frontier A = closure A \ interior A := by
    simpa using (frontier_eq_closure_diff_interior (X := X) (A := A))
  -- Substitute `closure A = univ` into the expression.
  simpa [h_closure] using h_frontier

theorem frontier_eq_closure_inter_compl_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (A : Set X) = closure A ∩ (interior A)ᶜ := by
  simpa [Set.diff_eq] using
    (frontier_eq_closure_diff_interior (X := X) (A := A))

theorem frontier_eq_empty_iff_clopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = (∅ : Set X) ↔ (IsOpen A ∧ IsClosed A) := by
  constructor
  · intro hFrontierEmpty
    -- Step 1: translate `frontier A = ∅` into `closure A \ interior A = ∅`.
    have hDiffEmpty : closure A \ interior A = (∅ : Set X) := by
      have hEq := (frontier_eq_closure_diff_interior (X := X) (A := A)).symm
      simpa [hFrontierEmpty] using hEq
    -- Step 2: deduce `closure A ⊆ interior A`.
    have hSub : closure A ⊆ interior A := by
      intro x hxCl
      by_cases hxInt : x ∈ interior A
      · exact hxInt
      · have hxInDiff : x ∈ closure A \ interior A := And.intro hxCl hxInt
        have : x ∈ (∅ : Set X) := by
          simpa [hDiffEmpty] using hxInDiff
        exact (by cases this)
    -- Step 3: establish `closure A = interior A`.
    have hEq_cl_int : closure A = interior A := by
      apply Set.Subset.antisymm hSub
      -- `interior A ⊆ closure A`
      intro x hxInt
      have hxA : x ∈ A := interior_subset hxInt
      exact subset_closure hxA
    -- Step 4: derive `interior A = A` and `closure A = A`.
    have hIntEqA : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · intro x hxA
        have hxCl : x ∈ closure A := subset_closure hxA
        simpa [hEq_cl_int] using hxCl
    have hClEqA : closure A = A := by
      simpa [hIntEqA] using hEq_cl_int
    -- Step 5: conclude that `A` is both open and closed.
    have hOpen : IsOpen A := by
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hIntEqA] using hOpenInt
    have hClosed : IsClosed A := by
      have hClosedCl : IsClosed (closure A) := isClosed_closure
      simpa [hClEqA] using hClosedCl
    exact And.intro hOpen hClosed
  · rintro ⟨hOpen, hClosed⟩
    -- A set that is both open and closed has empty frontier.
    simpa using
      (frontier_eq_empty_of_clopen (A := A) hOpen hClosed)

theorem frontier_interior_eq_closure_interior_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) = closure (interior A) \ interior A := by
  simpa [interior_interior]
    using
      (frontier_eq_closure_diff_interior (X := X) (A := interior A))

theorem frontier_closure_subset_closure_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure A) ⊆ closure (frontier A) := by
  intro x hx
  -- First, `frontier (closure A)` is contained in `frontier A`.
  have h₁ : frontier (closure A) ⊆ frontier A :=
    frontier_closure_subset_frontier (X := X) (A := A)
  -- Next, any point of `frontier A` lies in `closure (frontier A)`.
  have h₂ : frontier A ⊆ closure (frontier A) := by
    intro y hy
    exact subset_closure hy
  -- Combine the two inclusions to obtain the desired result.
  exact h₂ (h₁ hx)

theorem closure_inter_closure_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∩ closure B) = closure A ∩ closure B := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed (closure A ∩ closure B) :=
    (isClosed_closure : IsClosed (closure A)).inter
      (isClosed_closure : IsClosed (closure B))
  -- Taking the closure of a closed set leaves it unchanged.
  simpa using hClosed.closure_eq

theorem interior_union_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A ∪ interior A) = interior A := by
  -- Since `interior A ⊆ A`, the union is just `A`.
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA    => exact hA
      | inr hIntA => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  simpa [h_union]

theorem closure_interior_inter_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ closure (interior (closure A)) =
      closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    -- `closure (interior A)` is contained in `closure (interior (closure A))`
    have hx' :
        x ∈ closure (interior (closure A)) :=
      (closure_interior_subset_closure_interior_closure
        (X := X) (A := A)) hx
    exact And.intro hx hx'

theorem closure_inter_frontier_eq_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ frontier A = frontier A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hx_cl : x ∈ closure A :=
      (frontier_subset_closure (X := X) (A := A)) hx
    exact And.intro hx_cl hx

theorem interior_closure_frontier_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (frontier A)) = interior (frontier A) := by
  have h : closure (frontier A) = frontier A :=
    closure_frontier_eq_frontier (X := X) (A := A)
  simpa [h]

theorem closure_frontier_eq_closure_inter_closures {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (frontier A) = closure A ∩ closure (Aᶜ) := by
  -- `frontier A` is closed, hence its closure is itself.
  have h₁ : closure (frontier A) = frontier A :=
    closure_frontier_eq_frontier (X := X) (A := A)
  -- `frontier A` can also be expressed as the intersection of the two closures.
  have h₂ : frontier A = closure A ∩ closure (Aᶜ) :=
    (closure_inter_closure_compl_eq_frontier (X := X) (A := A)).symm
  -- Combine the two equalities.
  simpa [h₁] using h₂

theorem diff_frontier_eq_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    A \ frontier A = interior A := by
  ext x
  constructor
  · intro hx
    have hxA : x ∈ A := hx.1
    have hNotFront : x ∉ frontier A := hx.2
    -- If `x` were not in `interior A`, it would lie in the frontier,
    -- because points of `A` outside `interior A` belong to `frontier A`.
    by_cases hxInt : x ∈ interior A
    · exact hxInt
    · have hxFront : x ∈ frontier A := by
        -- `x ∈ closure A` since `A ⊆ closure A`.
        have hxCl : x ∈ closure A := subset_closure hxA
        exact And.intro hxCl hxInt
      exact (hNotFront hxFront).elim
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    -- Points of `interior A` are not in the frontier.
    have hNotFront : x ∉ frontier A := by
      intro hFront
      have : x ∈ (interior A)ᶜ :=
        (frontier_subset_compl_interior (X := X) (A := A)) hFront
      exact this hxInt
    exact And.intro hxA hNotFront

theorem frontier_interior_eq_frontier_inter_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) = frontier A ∩ closure (interior A) := by
  ext x
  constructor
  · intro hx
    -- `hx` provides membership in the closure of `interior A`
    -- and non‐membership in its interior.
    have hClInt  : x ∈ closure (interior A) := hx.1
    have hNotInt : x ∉ interior A := by
      -- `hx.2 : x ∉ interior (interior A)`; rewrite with `interior_interior`.
      simpa [interior_interior] using hx.2
    -- Use monotonicity of `closure` to pass from
    -- `closure (interior A)` to `closure A`.
    have hClA : x ∈ closure A := by
      have hSub : closure (interior A) ⊆ closure A :=
        closure_interior_subset_closure (A := A)
      exact hSub hClInt
    -- Assemble the membership in `frontier A`.
    have hFrontA : x ∈ frontier A := And.intro hClA hNotInt
    exact And.intro hFrontA hClInt
  · intro hx
    -- Extract the two components of the intersection.
    have hFrontA : x ∈ frontier A := hx.1
    have hClInt  : x ∈ closure (interior A) := hx.2
    -- From `frontier A`, obtain `x ∉ interior A`.
    have hNotInt : x ∉ interior A := hFrontA.2
    -- Rewrite the non‐membership for `interior (interior A)`.
    have hNotIntInt : x ∉ interior (interior A) := by
      simpa [interior_interior] using hNotInt
    -- Conclude membership in `frontier (interior A)`.
    exact And.intro hClInt hNotIntInt

theorem interior_union_frontier_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ frontier A = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxInt =>
        -- Points of `interior A` certainly lie in `closure A`.
        have hxA : x ∈ A := interior_subset hxInt
        exact subset_closure hxA
    | inr hxFront =>
        -- The frontier is contained in the closure.
        exact hxFront.1
  · intro hxCl
    -- Case split on whether `x` already lies in `interior A`.
    by_cases hxInt : x ∈ interior A
    · exact Or.inl hxInt
    · -- Otherwise, `x` belongs to the frontier.
      have hxFront : x ∈ frontier A := And.intro hxCl hxInt
      exact Or.inr hxFront

theorem closure_union_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B) = A ∪ B := by
  -- The union of two closed sets is closed.
  have hClosed : IsClosed (A ∪ B) := hA.union hB
  -- Taking the closure of a closed set leaves it unchanged.
  simpa [hClosed.closure_eq]

theorem frontier_diff_subset_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  -- First rewrite the difference as an intersection and apply the existing lemma
  have h :
      frontier (A \ B) ⊆ frontier A ∪ frontier (Bᶜ) := by
    simpa [Set.diff_eq] using
      (frontier_inter_subset (A := A) (B := Bᶜ))
  -- Replace `frontier (Bᶜ)` with `frontier B`
  simpa [frontier_compl_eq_frontier (A := B)] using h

theorem inter_frontier_eq_diff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    (A ∩ frontier A : Set X) = A \ interior A := by
  ext x
  constructor
  · intro hx
    exact And.intro hx.1 hx.2.2
  · intro hx
    have hx_cl : x ∈ closure A := subset_closure hx.1
    exact And.intro hx.1 (And.intro hx_cl hx.2)

theorem interior_closure_inter_eq_inter_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure (A ∩ B)) = interior A ∩ interior B := by
  -- `A ∩ B` is closed because both `A` and `B` are closed.
  have hABclosed : IsClosed (A ∩ B) := hA.inter hB
  -- Hence its closure is itself.
  have h_closure : closure (A ∩ B) = A ∩ B := hABclosed.closure_eq
  -- Rewrite and use the distributivity of `interior` over intersections.
  simpa [h_closure, interior_inter]

theorem frontier_eq_univ_of_dense_and_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → interior A = (∅ : Set X) → frontier (A : Set X) = (Set.univ : Set X) := by
  intro hDense hInt
  -- Use the previously established description of the frontier of a dense set.
  have h :=
    dense_frontier_eq_compl_interior (X := X) (A := A) hDense
  -- Substitute the hypothesis `interior A = ∅` and simplify.
  simpa [hInt, Set.diff_empty] using h

theorem frontier_univ_eq_empty {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  simpa [frontier_eq_closure_diff_interior, closure_univ, interior_univ]

theorem P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) := by
  exact
    And.intro
      (Topology.P1_univ (X := X))
      (And.intro
        (Topology.P2_univ (X := X))
        (Topology.P3_univ (X := X)))

theorem interior_closure_union_frontier_eq_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure A) ∪ frontier (A : Set X) = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hIntCl => exact interior_subset hIntCl
    | inr hFront => exact hFront.1
  · intro hxCl
    by_cases hIntCl : x ∈ interior (closure A)
    · exact Or.inl hIntCl
    ·
      have h_not_intA : x ∉ interior A := by
        intro hIntA
        have h_sub : interior A ⊆ interior (closure A) :=
          Topology.interior_subset_interior_closure (A := A)
        have : x ∈ interior (closure A) := h_sub hIntA
        exact hIntCl this
      have hFront : x ∈ frontier A := And.intro hxCl h_not_intA
      exact Or.inr hFront



theorem frontier_inter_subset_closure_pair
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- From `hx` we obtain membership in `closure (A ∩ B)`.
  have hx_cl : x ∈ closure (A ∩ B) := hx.1
  -- `closure (A ∩ B)` is contained in each of `closure A` and `closure B`.
  have hA : closure (A ∩ B) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : closure (A ∩ B) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact And.intro (hA hx_cl) (hB hx_cl)



theorem interior_diff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed B) :
    interior (A \ B) = interior A \ B := by
  ext x
  constructor
  · intro hx
    have hAB : x ∈ A \ B := interior_subset hx
    -- `A \ B ⊆ A`, hence `x ∈ interior A`
    have hIntA : x ∈ interior A := by
      have hSub : (A \ B : Set X) ⊆ A := fun y hy => hy.1
      exact (interior_mono hSub) hx
    exact And.intro hIntA hAB.2
  · rintro ⟨hxIntA, hxNotB⟩
    -- Build an open neighborhood contained in `A \ B`
    have hOpen : IsOpen (interior A ∩ Bᶜ) :=
      isOpen_interior.inter hB.isOpen_compl
    have hMem  : x ∈ interior A ∩ Bᶜ := And.intro hxIntA hxNotB
    have hSub  : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    -- Conclude that `x` belongs to `interior (A \ B)`
    have : (A \ B : Set X) ∈ nhds x :=
      Filter.mem_of_superset (hOpen.mem_nhds hMem) hSub
    exact (mem_interior_iff_mem_nhds).2 this

theorem frontier_inter_subset_frontier_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆
      (frontier A ∩ closure B) ∪ (frontier B ∩ closure A) := by
  intro x hx
  rcases hx with ⟨hx_clAB, hx_notIntAB⟩
  -- Membership in the individual closures.
  have hx_clA : x ∈ closure A := by
    have h : closure (A ∩ B) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact h hx_clAB
  have hx_clB : x ∈ closure B := by
    have h : closure (A ∩ B) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact h hx_clAB
  -- Case split on membership in `interior A`.
  by_cases hIntA : x ∈ interior A
  · -- Then `x ∉ interior B`, otherwise `x ∈ interior (A ∩ B)`.
    have hNotIntB : x ∉ interior B := by
      intro hIntB
      -- Build an open neighbourhood of `x` contained in `A ∩ B`.
      have h_open : IsOpen (interior A ∩ interior B) :=
        isOpen_interior.inter isOpen_interior
      have h_mem  : x ∈ interior A ∩ interior B := And.intro hIntA hIntB
      have h_sub  : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
        intro y hy
        exact And.intro (interior_subset hy.1) (interior_subset hy.2)
      have h_nhds : (A ∩ B : Set X) ∈ nhds x :=
        Filter.mem_of_superset (h_open.mem_nhds h_mem) h_sub
      have : x ∈ interior (A ∩ B) :=
        (mem_interior_iff_mem_nhds).2 h_nhds
      exact hx_notIntAB this
    -- Conclude `x ∈ frontier B ∩ closure A`.
    have hFrontB : x ∈ frontier B := And.intro hx_clB hNotIntB
    exact Or.inr (And.intro hFrontB hx_clA)
  · -- Otherwise `x ∉ interior A`, so `x ∈ frontier A ∩ closure B`.
    have hFrontA : x ∈ frontier A := And.intro hx_clA hIntA
    exact Or.inl (And.intro hFrontA hx_clB)

theorem frontier_subset_closure_diff_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (A : Set X) ⊆ closure A \ interior A := by
  intro x hx
  have hx_cl : x ∈ closure A :=
    frontier_subset_closure (X := X) (A := A) hx
  have hx_not_int : x ∉ interior A :=
    (frontier_subset_compl_interior (X := X) (A := A)) hx
  exact And.intro hx_cl hx_not_int

theorem interior_closure_inter_subset_interior_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A ∩ closure B) := by
  intro x hx
  have hsubset : closure (A ∩ B) ⊆ closure A ∩ closure B :=
    closure_inter_subset_inter_closure (A := A) (B := B)
  exact (interior_mono hsubset) hx

theorem closure_diff_subset_closure_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  -- The set difference `A \ B` is clearly contained in `A`.
  have h_sub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h_sub

theorem isClosed_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ⊆ A → IsClosed A := by
  intro h
  have hEq : closure A = A := subset_antisymm h subset_closure
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa [hEq] using hClosed

theorem interior_eq_closure_iff_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = closure A ↔ (IsOpen A ∧ IsClosed A) := by
  constructor
  · intro h_eq
    -- First, show `interior A = A`.
    have hA_int : A ⊆ interior A := by
      intro x hx
      have hx_cl : x ∈ closure A := subset_closure hx
      simpa [h_eq] using hx_cl
    have h_int_eq : interior A = A :=
      subset_antisymm interior_subset hA_int
    -- Next, deduce `closure A = A`.
    have h_cl_eq : closure A = A := by
      calc
        closure A = interior A := by
          simpa [h_eq]
        _ = A := h_int_eq
    -- Conclude that `A` is both open and closed.
    have h_open : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [h_int_eq] using this
    have h_closed : IsClosed A := by
      have : IsClosed (closure A) := isClosed_closure
      simpa [h_cl_eq] using this
    exact And.intro h_open h_closed
  · rintro ⟨h_open, h_closed⟩
    simpa [h_open.interior_eq, h_closed.closure_eq]

theorem frontier_subset_compl_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    frontier (A : Set X) ⊆ Aᶜ := by
  have h := frontier_subset_compl_interior (X := X) (A := A)
  simpa [hA.interior_eq] using h

theorem frontier_interior_subset_closure_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) ⊆ closure (frontier A) := by
  intro x hx
  -- `frontier (interior A)` is contained in `frontier A`.
  have h_subset : frontier (interior A) ⊆ frontier A :=
    frontier_interior_subset_frontier (X := X) (A := A)
  -- Hence `x` belongs to `frontier A`.
  have hx_frontier : x ∈ frontier A := h_subset hx
  -- Every point of a set lies in the closure of that set.
  exact subset_closure hx_frontier

theorem frontier_frontier_subset_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    frontier (frontier (A : Set X)) ⊆ A := by
  intro x hx
  -- Step 1: `frontier A ⊆ A` because `A` is closed.
  have h_sub : frontier A ⊆ A :=
    frontier_subset_of_closed (A := A) hA
  -- Step 2: Taking closures preserves inclusions, and `closure A = A`.
  have h_closure : closure (frontier A) ⊆ A := by
    have h := closure_mono h_sub
    simpa [hA.closure_eq] using h
  -- Step 3: `x` lies in `closure (frontier A)` by definition of the frontier,
  -- hence in `A` by `h_closure`.
  exact h_closure hx.1

theorem closure_frontier_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier A) = closure A \ interior A := by
  calc
    closure (frontier A)
        = frontier A := by
          simpa using
            (closure_frontier_eq_frontier (X := X) (A := A))
    _   = closure A \ interior A := by
          simpa using
            (frontier_eq_closure_diff_interior (X := X) (A := A))



theorem frontier_union_subset_frontier_left_union_closure_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B : Set X) ⊆ frontier A ∪ closure B := by
  intro x hx
  rcases hx with ⟨hx_cl_union, hx_not_int_union⟩
  by_cases hB : x ∈ closure B
  · exact Or.inr hB
  ·
    -- First, rewrite `closure (A ∪ B)` as `closure A ∪ closure B`
    have hx_clA_or : x ∈ closure A ∪ closure B := by
      have h_eq := closure_union (s := A) (t := B)
      simpa [h_eq] using hx_cl_union
    -- Since `x ∉ closure B`, we deduce `x ∈ closure A`
    have hx_clA : x ∈ closure A := by
      cases hx_clA_or with
      | inl hA   => exact hA
      | inr hB'  => exact (hB hB').elim
    -- Show that `x ∉ interior A`
    have hx_not_intA : x ∉ interior A := by
      intro hx_intA
      -- `interior A ⊆ interior (A ∪ B)` by monotonicity
      have hx_int_union : x ∈ interior (A ∪ B) := by
        have h_subset :
            interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact h_subset hx_intA
      exact hx_not_int_union hx_int_union
    -- Therefore `x ∈ frontier A`
    have hx_frontA : x ∈ frontier A := And.intro hx_clA hx_not_intA
    exact Or.inl hx_frontA

theorem interior_frontier_eq_empty_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    interior (frontier A) = (∅ : Set X) := by
  -- Rewrite the frontier using the fact that `A` is closed.
  have hFrontier : (frontier A : Set X) = A \ interior A :=
    frontier_eq_diff_interior_of_closed (A := A) hA
  -- Show that `interior (A \ interior A)` is empty.
  have hEmpty : interior (A \ interior A : Set X) = (∅ : Set X) := by
    apply Set.Subset.antisymm
    · intro x hx
      -- `x ∈ A \ interior A`
      have hxDiff : x ∈ A \ interior A := interior_subset hx
      -- `x ∈ interior A`, since interiors are monotone and
      -- `(A \ interior A) ⊆ A`.
      have hSub : (A \ interior A : Set X) ⊆ A := by
        intro y hy; exact hy.1
      have hxIntA : x ∈ interior A := (interior_mono hSub) hx
      -- Contradiction with `x ∉ interior A`.
      exact (hxDiff.2 hxIntA).elim
    · exact Set.empty_subset _
  -- Use the two identities obtained above.
  calc
    interior (frontier A)
        = interior (A \ interior A) := by
          simpa [hFrontier]
    _   = (∅ : Set X) := hEmpty

theorem interior_closure_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) \ interior A ⊆ frontier A := by
  intro x hx
  -- Extract the two conditions from the set difference.
  have hxIntClosure : x ∈ interior (closure A) := hx.1
  have hxNotIntA : x ∉ interior A := hx.2
  -- Any point of `interior (closure A)` lies in `closure A`.
  have hxClosureA : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntClosure
  -- Combine the facts to obtain membership in the frontier.
  exact And.intro hxClosureA hxNotIntA



theorem interior_frontier_eq_empty_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    interior (frontier (A : Set X)) = (∅ : Set X) := by
  -- The complement of an open set is closed.
  have hClosed : IsClosed (Aᶜ) := hA.isClosed_compl
  -- For a closed set, the interior of its frontier is empty.
  have h₁ : interior (frontier (Aᶜ)) = (∅ : Set X) :=
    interior_frontier_eq_empty_of_closed (A := Aᶜ) hClosed
  -- The frontier is invariant under taking complements.
  have h₂ : frontier (Aᶜ) = frontier (A : Set X) :=
    frontier_compl_eq_frontier (A := A)
  -- Rewrite using `h₂` and conclude.
  simpa [h₂] using h₁

theorem interior_closure_diff_closure_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) \ closure (interior A) ⊆ frontier A := by
  intro x hx
  -- `hx` gives membership in the interior of `closure A`
  -- and non-membership in `closure (interior A)`.
  have hxIntCl : x ∈ interior (closure A) := hx.1
  have hxNotClInt : x ∉ closure (interior A) := hx.2
  -- Any point of `interior (closure A)` lies in `closure A`.
  have hxClA : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntCl
  -- Show that `x` is not in `interior A`; otherwise we contradict `hxNotClInt`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    -- `interior A` is contained in its closure, contradicting `hxNotClInt`.
    have : x ∈ closure (interior A) := subset_closure hxIntA
    exact hxNotClInt this
  -- Assemble the two conditions defining `frontier A`.
  exact And.intro hxClA hxNotIntA

theorem frontier_eq_closure_of_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = (∅ : Set X)) :
    frontier A = closure A := by
  have h := (frontier_eq_closure_diff_interior (X := X) (A := A))
  simpa [hInt, Set.diff_empty] using h



theorem frontier_frontier_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (frontier (A : Set X)) ⊆ closure A := by
  intro x hx
  have hx_frontier : x ∈ frontier A :=
    (frontier_frontier_subset_frontier (X := X) (A := A)) hx
  exact (frontier_subset_closure (X := X) (A := A)) hx_frontier

theorem closure_diff_subset_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A ∩ closure (Bᶜ) := by
  intro x hx
  -- `A \ B` is contained in `A`, hence its closure is contained in `closure A`.
  have hA : x ∈ closure A := by
    have h_sub : (A \ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact (closure_mono h_sub) hx
  -- `A \ B` is also contained in `Bᶜ`, yielding membership in `closure (Bᶜ)`.
  have hB : x ∈ closure (Bᶜ) := by
    have h_sub : (A \ B : Set X) ⊆ Bᶜ := by
      intro y hy; exact hy.2
    exact (closure_mono h_sub) hx
  exact And.intro hA hB

theorem closure_inter_closure_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  have h :=
    closure_inter_subset_inter_closure
      (A := A) (B := closure B)
  simpa [closure_closure] using h

theorem frontier_eq_closure_inter_compl_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    frontier A = closure A ∩ Aᶜ := by
  -- Start from the general characterization
  -- `frontier A = closure A ∩ (interior A)ᶜ`.
  have h :=
    frontier_eq_closure_inter_compl_interior (X := X) (A := A)
  -- For an open set `A` we have `interior A = A`, so the right‐hand side
  -- simplifies to `closure A ∩ Aᶜ`.
  simpa [hA.interior_eq] using h

theorem frontier_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxFront : x ∈ frontier A := hx.1
    have hxIntComp : x ∈ interior (Aᶜ) := hx.2
    -- `interior (Aᶜ)` is the complement of `closure A`
    have hIntEq : interior (Aᶜ : Set X) = (closure A)ᶜ :=
      interior_compl_eq_compl_closure (A := A)
    have hxNotClosure : x ∉ closure A := by
      have : x ∈ (closure A)ᶜ := by
        simpa [hIntEq] using hxIntComp
      exact this
    have hxClosure : x ∈ closure A := hxFront.1
    have hFalse : False := hxNotClosure hxClosure
    exact False.elim hFalse
  · exact Set.empty_subset _

theorem closure_compl_diff_interior_compl_eq_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (Aᶜ) \ interior (Aᶜ) = frontier (A : Set X) := by
  calc
    closure (Aᶜ) \ interior (Aᶜ)
        = frontier (Aᶜ) := by
          simpa using
            (frontier_eq_closure_diff_interior (X := X) (A := Aᶜ)).symm
    _ = frontier (A : Set X) := by
          simpa using
            (frontier_compl_eq_frontier (X := X) (A := A))

theorem interior_compl_eq_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    interior (Aᶜ) = Aᶜ := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  simpa using hOpen.interior_eq

theorem closure_diff_frontier_eq_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A \ frontier A = interior A := by
  ext x
  constructor
  · intro hx
    have hxCl : x ∈ closure A := hx.1
    have hNotFront : x ∉ frontier A := hx.2
    by_contra hNotInt
    have hFront : x ∈ frontier A := And.intro hxCl hNotInt
    exact hNotFront hFront
  · intro hxInt
    have hxCl : x ∈ closure A := subset_closure (interior_subset hxInt)
    have hNotFront : x ∉ frontier A := by
      intro hFront
      exact hFront.2 hxInt
    exact And.intro hxCl hNotFront

theorem frontier_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → frontier (A : Set X) ⊆ closure (interior A) := by
  intro hP1
  intro x hxFront
  -- `hxFront` gives `x ∈ closure A`.
  have hx_cl : x ∈ closure A := hxFront.1
  -- Under `P1`, the two closures coincide.
  have h_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Rewrite and conclude.
  simpa [h_eq] using hx_cl

theorem isOpen_of_frontier_subset_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ Aᶜ → IsOpen A := by
  intro hFront
  -- First, show `A ⊆ interior A`.
  have hSub : (A : Set X) ⊆ interior A := by
    intro x hxA
    by_cases hxInt : x ∈ interior A
    · exact hxInt
    · -- Otherwise `x` lies in the frontier, contradicting the hypothesis.
      have hxFrontier : x ∈ frontier A := by
        have hxCl : x ∈ closure A := subset_closure hxA
        exact And.intro hxCl hxInt
      have hxCompl : x ∈ Aᶜ := hFront hxFrontier
      exact (hxCompl hxA).elim
  -- Hence `interior A = A`.
  have hEq : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    · exact hSub
  -- Conclude that `A` is open.
  simpa [hEq] using (isOpen_interior : IsOpen (interior A))

theorem closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ interior (Aᶜ) = (∅ : Set X) := by
  -- Rewrite `interior (Aᶜ)` using the complement–closure formula.
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  -- The intersection of a set with its complement is empty.
  simpa [h] using (Set.inter_compl_self (closure A))

theorem frontier_closure_eq_empty_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → frontier (closure A) = (∅ : Set X) := by
  intro hDense
  have h_closure_univ : (closure A : Set X) = Set.univ := hDense.closure_eq
  simpa [h_closure_univ, frontier_univ_eq_empty (X := X)]

theorem closure_diff_interior_compl_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A \ interior A = closure (Aᶜ) \ interior (Aᶜ) := by
  -- Rewrite each difference using the `frontier` of the corresponding set.
  have h₁ :
      closure A \ interior A = frontier (A : Set X) := by
    simpa using
      (frontier_eq_closure_diff_interior (X := X) (A := A)).symm
  have h₂ :
      closure (Aᶜ) \ interior (Aᶜ) = frontier (Aᶜ) := by
    simpa using
      (frontier_eq_closure_diff_interior (X := X) (A := Aᶜ)).symm
  -- The frontier is invariant under taking complements.
  have h_front : frontier (Aᶜ) = frontier (A : Set X) :=
    frontier_compl_eq_frontier (X := X) (A := A)
  -- Chain the equalities to reach the goal.
  calc
    closure A \ interior A
        = frontier (A : Set X) := h₁
    _   = frontier (Aᶜ) := by
          simpa using h_front.symm
    _   = closure (Aᶜ) \ interior (Aᶜ) := by
          simpa using
            (frontier_eq_closure_diff_interior (X := X) (A := Aᶜ))