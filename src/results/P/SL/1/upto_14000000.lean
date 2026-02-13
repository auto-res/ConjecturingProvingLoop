

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  exact Set.Subset.trans h interior_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at hA ⊢
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hclosure : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono hclosure
  exact Set.Subset.trans hA hsubset

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    (by
      have hsubset : interior A ⊆ closure (interior A) := by
        intro x hx
        exact subset_closure hx
      have hmono : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono hsubset
      simpa [interior_interior] using hmono)

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  dsimp [Topology.P3]
  have h : interior (interior A) ⊆ interior (closure (interior A)) := by
    apply interior_mono
    intro x hx
    exact subset_closure hx
  simpa [interior_interior] using h

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  simpa [interior_interior] using
    (subset_closure : interior A ⊆ closure (interior A))

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  dsimp [Topology.P1]
  simpa using (subset_closure : interior (closure A) ⊆ closure (interior (closure A)))

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  simp

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  simpa using
    (Set.empty_subset : (∅ : Set X) ⊆ interior (closure (∅ : Set X)))

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  have h : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  simpa [hA.interior_eq] using h

theorem P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have h : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  simpa [hA.interior_eq] using h

theorem P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  simpa [hA.interior_eq] using (subset_closure : A ⊆ closure A)

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  dsimp [Topology.P2]
  have hsubset : interior (closure A) ⊆ closure (interior (closure A)) := by
    intro x hx
    exact subset_closure hx
  have hmono :
      interior (interior (closure A)) ⊆ interior (closure (interior (closure A))) :=
    interior_mono hsubset
  simpa [interior_interior] using hmono

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA.closure_eq]
  have hsub : (A : Set X) ⊆ interior (closure A) := by
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hInt] using this
  simpa using hsub

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  simpa using (P3_interior (A := closure A))

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intros hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxInt : x ∈ interior (closure A) := hA hxA
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hxInt
  | inr hxB =>
      have hxInt : x ∈ interior (closure B) := hB hxB
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_right
        exact this
      exact hsubset hxInt

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intros hA hB
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          have hAB : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hAB
        exact this
      exact hsubset hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) := by
          have hBA : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hBA
        exact this
      exact hsubset hx_closure

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxInt : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
        have h₁ : interior A ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono this
        have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hsubset hxInt
  | inr hxB =>
      have hxInt : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
        have h₁ : interior B ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono this
        have h₂ : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hsubset hxInt

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  simpa using
    (Set.empty_subset :
      (∅ : Set X) ⊆ interior (closure (interior (∅ : Set X))))

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem Topology.closure_interior_eq_of_isClosed_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP1 : Topology.P1 A) :
    closure (interior A) = A := by
  apply Set.Subset.antisymm
  ·
    have hsubset : interior A ⊆ A := interior_subset
    have hclosure : closure (interior A) ⊆ closure A := closure_mono hsubset
    simpa [hA.closure_eq] using hclosure
  ·
    exact hP1

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h.closure_eq, interior_univ] using this

theorem Topology.P1_iff_closure_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_of_isClosed_of_P1 hA hP1
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    simpa [hEq] using hx

theorem Topology.P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    dsimp [Topology.P3] at hP3
    have hsubset1 : (A : Set X) ⊆ interior A := by
      simpa [hA.closure_eq] using hP3
    have hsubset2 : interior A ⊆ A := interior_subset
    have hEq : interior A = A := Set.Subset.antisymm hsubset2 hsubset1
    have : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using this
  · intro hOpen
    exact Topology.P3_of_isOpen hOpen

theorem Topology.closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure A = closure (interior A) := by
  intro hP1
  apply Set.Subset.antisymm
  ·
    have hsub : (A : Set X) ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hsub
    simpa using this
  ·
    have hsub : interior A ⊆ (A : Set X) := interior_subset
    have : closure (interior A) ⊆ closure A := closure_mono hsub
    simpa using this

theorem Topology.P1_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = closure (interior A)) :
    Topology.P1 A := by
  dsimp [Topology.P1] at *
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  simpa [h] using hx_closure

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact P2_implies_P3 (A := A) hP2
  · intro hP3
    dsimp [Topology.P2, Topology.P3] at hP3 ⊢
    simpa [hA.interior_eq] using hP3

theorem Topology.P1_iff_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  · intro hEq
    exact Topology.P1_of_closure_eq_closure_interior (A := A) hEq

theorem Topology.P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  intro x hx
  have hA_subset : (A : Set X) ⊆ interior (closure A) := by
    apply interior_maximal
    · exact subset_closure
    · exact hA
  have hclosure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hA_subset
  exact hclosure_subset hx

theorem Topology.P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  -- Step 1: turn `x ∈ closure A` into `x ∈ closure (interior A)`
  have hsubset1 : closure A ⊆ closure (interior A) := by
    have htemp : closure A ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using htemp
  -- Step 2: upgrade to `x ∈ closure (interior (closure A))`
  have hsubset2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have htemp : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono htemp
  exact hsubset2 (hsubset1 hx)

theorem Topology.P2_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := P2_implies_P3 (A := A) hP2
    exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  · intro hOpen
    exact Topology.P2_of_isOpen (A := A) hOpen

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure A) := by
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h.closure_eq] using this

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  exact Set.Subset.trans interior_subset subset_closure

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- We show `closure (interior A)` is contained in `closure (interior (closure (interior A)))`.
  have hsubset : closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    -- First, monotonicity of `interior` gives the needed inclusion of interiors.
    have hInner : interior (interior A) ⊆ interior (closure (interior A)) := by
      apply interior_mono
      exact (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    -- Taking closures preserves inclusion.
    have hclosure : closure (interior (interior A)) ⊆
        closure (interior (closure (interior A))) := closure_mono hInner
    simpa [interior_interior] using hclosure
  exact hsubset hx

theorem Topology.closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure A = closure (interior A) := by
  intro hP2
  apply Set.Subset.antisymm
  ·
    -- First, `closure A ⊆ closure (interior (closure (interior A)))`
    have h1 : closure A ⊆ closure (interior (closure (interior A))) :=
      closure_mono hP2
    -- Next, `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h2 : closure (interior (closure (interior A))) ⊆ closure (interior A) := by
      have hinner : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      have hclosure : closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
        closure_mono hinner
      simpa [closure_closure] using hclosure
    exact Set.Subset.trans h1 h2
  ·
    -- The reverse inclusion `closure (interior A) ⊆ closure A`
    have hsub : interior A ⊆ (A : Set X) := interior_subset
    exact closure_mono hsub

theorem Topology.closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    have h : (A : Set X) ⊆ interior (closure A) := hP3
    simpa using (closure_mono h)
  ·
    have h : interior (closure A) ⊆ closure A := interior_subset
    simpa [closure_closure] using (closure_mono h)

theorem Topology.closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure A) → closure (interior (closure A)) = closure A := by
  intro hP1
  simpa using
    (Topology.closure_interior_eq_of_isClosed_of_P1 (A := closure A) isClosed_closure hP1)

theorem Topology.P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  have hEq : closure A = closure (interior (closure A)) :=
    Topology.closure_eq_closure_interior_closure_of_P3 (A := A) hP3
  have hP1 : Topology.P1 (closure A) :=
    Topology.P1_of_closure_eq_closure_interior
      (A := closure A)
      (by
        simpa [closure_closure] using hEq)
  exact hP1

theorem Topology.P1_iUnion_interior {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (A : ι → Set X) : Topology.P1 (⋃ i, interior (A i)) := by
  -- First, show that the union of the interiors is an open set.
  have hOpen : IsOpen (⋃ i, interior (A i)) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  -- Apply `P1_of_isOpen` to conclude the desired result.
  exact Topology.P1_of_isOpen (A := ⋃ i, interior (A i)) hOpen

theorem Topology.P2_iff_P3_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h1 : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (A := A) hA
  have h2 : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (A := A) hA
  simpa using h1.trans h2.symm

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ Topology.P3 (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P2_iff_P3_of_isClosed (A := closure A) hClosed)

theorem Topology.P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A := P2_implies_P3 (A := A) hP2
  exact Topology.P1_closure_of_P3 (A := A) hP3

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  have h₁ : interior A ⊆ A := interior_subset
  have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
  exact interior_mono h₂

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P3 (A i)) → Topology.P3 (⋃ i, A i) := by
  intro hA
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hxInt : x ∈ interior (closure (A i)) := (hA i) hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ i, A i)) := by
    apply interior_mono
    have : closure (A i) ⊆ closure (⋃ i, A i) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hsubset hxInt

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P1 (A i)) → Topology.P1 (⋃ i, A i) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx_closure : x ∈ closure (interior (A i)) := (hA i) hxAi
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    apply closure_mono
    have : interior (A i) ⊆ interior (⋃ j, A j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hsubset hx_closure

theorem Topology.isOpen_of_P2_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) :
    IsOpen A := by
  exact (Topology.P2_iff_isOpen_of_isClosed (A := A) hA).1 hP2

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P2 (⋃ i, A i) := by
  intro hA
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hxInt : x ∈ interior (closure (interior (A i))) := (hA i) hxAi
  have hsubset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    apply interior_mono
    have : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      apply closure_mono
      have : interior (A i) ⊆ interior (⋃ j, A j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact this
    exact this
  exact hsubset hxInt

theorem Topology.P3_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed A → IsClosed B → Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hA_closed hB_closed hA_P3 hB_P3
  -- From `P3` and closedness we obtain that `A` and `B` are open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hA_P3
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (A := B) hB_closed).1 hB_P3
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA_open.inter hB_open
  -- An open set always satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A ∩ B) hOpen

theorem Topology.P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed A → IsClosed B → Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hA_closed hB_closed hA_P2 hB_P2
  -- From `P2` and closedness we obtain that `A` and `B` are open.
  have hA_open : IsOpen A :=
    (Topology.isOpen_of_P2_of_isClosed (A := A) hA_closed hA_P2)
  have hB_open : IsOpen B :=
    (Topology.isOpen_of_P2_of_isClosed (A := B) hB_closed hB_P2)
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA_open.inter hB_open
  -- An open set always satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A ∩ B) hOpen

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _; exact Topology.P2_of_isOpen (A := A) hA
  · intro _; exact Topology.P1_of_isOpen (A := A) hA

theorem Topology.P1_iff_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h1 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h2 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  exact h1.trans h2

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  -- First, show that `closure A = univ`.
  have hclosureA : closure A = (Set.univ : Set X) := by
    -- Since `interior A ⊆ A`, we get `closure (interior A) ⊆ closure A`.
    have hmono : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- But `closure (interior A) = univ` because `interior A` is dense.
    have hsubset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h.closure_eq] using hmono
    -- The reverse inclusion always holds.
    have hsubset' : closure A ⊆ (Set.univ : Set X) := by
      intro y hy
      simp
    exact Set.Subset.antisymm hsubset' hsubset
  -- With `closure A = univ`, its interior is also `univ`.
  have : x ∈ interior (closure A) := by
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hclosureA, interior_univ] using this
  exact this

theorem Topology.closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro _ _
    simp
  ·
    have hmono : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    have : closure (interior A) = (Set.univ : Set X) := by
      simpa using h.closure_eq
    simpa [this] using hmono

theorem closure_interior_univ_eq_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2
  -- Obtain `P3` for `closure A` from `P2`.
  have hP3_closure : Topology.P3 (closure A) :=
    P2_implies_P3 (A := closure A) hP2
  -- Unfold definitions to work with subset relations.
  dsimp [Topology.P3] at hP3_closure ⊢
  intro x hx
  -- Since `A ⊆ closure A`, upgrade `x` to a point of `closure A`.
  have hx_closure : x ∈ closure A := subset_closure hx
  -- Apply `P3` for `closure A`.
  have : x ∈ interior (closure (closure A)) := hP3_closure hx_closure
  -- Simplify `closure (closure A)` to conclude.
  simpa [closure_closure] using this

theorem Topology.P3_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure A) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  have hEq : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDense
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [closure_closure, hEq, interior_univ] using this

theorem Topology.P1_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  exact Topology.P1_of_isOpen (A := A ∩ B) hOpen

theorem Topology.P3_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A ∩ B) hOpen

theorem Topology.P2_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior A))) := by
  -- The set `interior (closure (interior A))` is open, so it automatically satisfies `P2`.
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P2_of_isOpen (A := interior (closure (interior A))) hOpen

theorem Topology.interior_closure_eq_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have hcl : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  simpa using congrArg (fun S : Set X => interior S) hcl

theorem Topology.P2_iUnion_interior {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (A : ι → Set X) : Topology.P2 (⋃ i, interior (A i)) := by
  -- The union of the interiors is an open set.
  have hOpen : IsOpen (⋃ i, interior (A i)) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := ⋃ i, interior (A i)) hOpen

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have hclosure :
        closure (interior (closure (interior A))) ⊆ closure (closure (interior A)) :=
      closure_mono hsubset
    simpa [closure_closure] using hclosure
  ·
    -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have hsubset : interior A ⊆ interior (closure (interior A)) := by
      -- Apply monotonicity of `interior` to the inclusion `interior A ⊆ closure (interior A)`.
      have : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      simpa [interior_interior] using interior_mono this
    have hclosure :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono hsubset
    exact hclosure

theorem Topology.P2_of_P3_and_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hEq : closure A = closure (interior A)) :
    Topology.P2 A := by
  dsimp [Topology.P2, Topology.P3] at hP3 ⊢
  intro x hx
  have hxInt : x ∈ interior (closure A) := hP3 hx
  have hIntEq : interior (closure A) = interior (closure (interior A)) := by
    simpa using congrArg (fun S : Set X => interior S) hEq
  simpa [hIntEq] using hxInt

theorem Topology.P2_closure_iff_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P2_iff_isOpen_of_isClosed (A := closure A) hClosed)

theorem Topology.P1_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) := by
  -- The set `interior (closure (interior A))` is open, hence it satisfies `P1`.
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P1_of_isOpen (A := interior (closure (interior A))) hOpen

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- First, retrieve the existing equivalences for open sets.
  have h1 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h2 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  -- Combine them into the desired equivalence with a conjunction.
  constructor
  · intro hP1
    exact And.intro (h1.mp hP1) (h2.mp hP1)
  · rintro ⟨hP2, _⟩
    exact h1.mpr hP2

theorem Topology.interior_closure_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa using
    congrArg (fun S : Set X => interior S) (closure_closure : closure (closure A) = closure A)

theorem Topology.P3_iUnion_interior {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (A : ι → Set X) : Topology.P3 (⋃ i, interior (A i)) := by
  -- The union of interiors is an open set.
  have hOpen : IsOpen (⋃ i, interior (A i)) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := ⋃ i, interior (A i)) hOpen

theorem Topology.P1_closure_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P1 (closure A) := by
  intro hDense
  have hP3 : Topology.P3 A := Topology.P3_of_dense_interior (A := A) hDense
  exact Topology.P1_closure_of_P3 (A := A) hP3

theorem Topology.P3_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior A))) := by
  -- The set `interior (closure (interior A))` is open, hence it satisfies `P3`.
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.P3_of_isOpen (A := interior (closure (interior A))) hOpen

theorem Topology.P1_iff_P2_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _; exact Topology.P2_of_dense_interior (A := A) h
  · intro _; exact Topology.P1_of_dense_interior (A := A) h

theorem Topology.P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  exact Topology.P1_of_isOpen (A := A) hOpen

theorem Topology.P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  exact
    Topology.P2_of_P3_and_closure_eq_closure_interior
      (A := A) hP3 hEq

theorem Topology.P2_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  exact Topology.P2_of_isOpen (A := A ∩ B) hOpen

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  have : x ∈ interior (closure (closure A)) := hP3 hx_closure
  simpa [closure_closure] using this

theorem Topology.P1_iff_P3_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) :
    Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro _; exact Topology.P3_of_dense_interior (A := A) h
  · intro _; exact Topology.P1_of_dense_interior (A := A) h

theorem Topology.P1_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P1 (closure A) := by
  intro hP2
  -- From `P2 (closure A)` we get that `closure A` is open.
  have hOpen : IsOpen (closure A) :=
    (Topology.P2_closure_iff_isOpen_closure (A := A)).1 hP2
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := closure A) hOpen

theorem Topology.P3_closure_iff_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P3_iff_isOpen_of_isClosed (A := closure A) hClosed)

theorem Topology.P1_closure_closure_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (closure A)) ↔ Topology.P1 (closure A) := by
  -- Useful equalities for rewriting.
  have hInt :
      interior (closure (closure A)) = interior (closure A) := by
    simpa using
      Topology.interior_closure_closure_eq_interior_closure (A := A)
  have hCl : closure (closure A) = closure A := by
    simpa [closure_closure] using rfl
  -- Prove each direction of the equivalence.
  constructor
  · intro hP
    dsimp [Topology.P1] at hP ⊢
    intro x hx
    -- View `x` as an element of `closure (closure A)` to use `hP`.
    have hx' : x ∈ closure (closure A) := by
      simpa [hCl] using hx
    -- Apply `hP` and rewrite with the interior equality.
    have : x ∈ closure (interior (closure (closure A))) := hP hx'
    simpa [hInt] using this
  · intro hP
    dsimp [Topology.P1] at hP ⊢
    intro x hx
    -- Rewrite `x` into an element of `closure A` to use `hP`.
    have hx' : x ∈ closure A := by
      simpa [hCl] using hx
    -- Apply `hP` and rewrite with the interior equality.
    have : x ∈ closure (interior (closure A)) := hP hx'
    simpa [hInt] using this

theorem Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  -- Use the existing equality of closures and apply `interior` to both sides.
  have h :=
    (Topology.closure_interior_closure_interior_eq_closure_interior
      (A := A))
  simpa using congrArg (fun S : Set X => interior S) h

theorem Topology.P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact And.intro (P2_implies_P1 (A := A) hP2) (P2_implies_P3 (A := A) hP2)
  · rintro ⟨hP1, hP3⟩
    exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3

theorem Topology.P2_iff_P3_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro _; exact Topology.P3_of_dense_interior (A := A) h
  · intro _; exact Topology.P2_of_dense_interior (A := A) h

theorem Topology.subset_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    (A : Set X) ⊆ interior (closure A) := by
  exact interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA

theorem Topology.interior_closure_eq_interior_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  -- From `P1` we know the closures are equal.
  have hcl : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Taking `interior` of both sides yields the desired equality.
  simpa using congrArg (fun S : Set X => interior S) hcl

theorem Topology.P2_of_P3_and_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A)
    (hEq : interior (closure A) = interior (closure (interior A))) :
    Topology.P2 A := by
  dsimp [Topology.P2, Topology.P3] at hP3 ⊢
  intro x hx
  have hx_int : x ∈ interior (closure A) := hP3 hx
  simpa [hEq] using hx_int

theorem Topology.isOpen_of_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A → IsOpen A := by
  intro hP3
  exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3

theorem Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (Topology.closure_interior_closure_interior_eq_closure_interior
      (A := closure A))

theorem Topology.P3_union_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → B ⊆ interior (closure A) → Topology.P3 (A ∪ B) := by
  intros hA hB
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- Points coming from `A` are handled by `hA`.
      have hxInt : x ∈ interior (closure A) := hA hxA
      -- Monotonicity of `interior` and `closure` upgrades the membership.
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hxInt
  | inr hxB =>
      -- Points coming from `B` are in `interior (closure A)` by assumption.
      have hxInt : x ∈ interior (closure A) := hB hxB
      -- As above, upgrade the membership.
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hxInt

theorem Topology.P2_iff_P1_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Established equivalences for open sets.
  have h1 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h2 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  -- Prove each direction of the desired equivalence.
  constructor
  · intro hP2
    have hP1 : Topology.P1 A := h1.mpr hP2
    have hP3 : Topology.P3 A := h2.mp hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    exact h1.mp hP1

theorem Topology.interior_closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) :
    interior (closure A) = (Set.univ : Set X) := by
  -- Since `interior A` is dense, its closure is the whole space.
  have h_closure : closure (interior A) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Monotonicity of `interior` and `closure` gives a useful inclusion.
  have h_mono : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    have : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    exact this
  -- Establish the desired equality by two inclusions.
  apply Set.Subset.antisymm
  · -- Trivial inclusion.
    intro x _
    simp
  · -- Use the density information to obtain the reverse inclusion.
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := by
      simpa [h_closure, interior_univ] using hx
    exact h_mono hx'

theorem Topology.P2_closure_closure_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  dsimp [Topology.P2]
  simpa [closure_closure]

theorem Topology.P2_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 (closure A) := by
  intro hDense
  -- First, `closure A` is the whole space because `interior A` is dense.
  have hclosure : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDense
  -- Unfold the definition of `P2` and prove the subset relation.
  dsimp [Topology.P2]
  intro x hx
  -- After rewriting everything in terms of `univ`, the goal becomes tautological.
  simpa [hclosure, interior_univ, closure_univ] using
    (by
      have : x ∈ (Set.univ : Set X) := by
        simp
      simpa using this)

theorem Topology.P3_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  simpa [h.interior_eq] using hx_closure

theorem Topology.P1_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → B ⊆ closure (interior A) → Topology.P1 (A ∪ B) := by
  intros hA hB
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- The point comes from `A`; use `P1` for `A`.
      have hx_closure : x ∈ closure (interior A) := hA hxA
      -- Upgrade the membership via monotonicity of `interior` and `closure`.
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hsubset hx_closure
  | inr hxB =>
      -- The point comes from `B`; use the subset assumption.
      have hx_closure : x ∈ closure (interior A) := hB hxB
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hsubset hx_closure

theorem Topology.closure_interior_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem Topology.P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = (Set.univ : Set X)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h, interior_univ] using this

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hA
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hxInt : x ∈ interior (closure A) := (hA A hA_mem) hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    have : closure A ⊆ closure (⋃₀ 𝒜) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact this
  exact hsubset hxInt

theorem Topology.P2_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → B ⊆ interior (closure (interior A)) → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  -- A handy inclusion used in both cases.
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (A ∪ B))) := by
    -- First, `interior A ⊆ interior (A ∪ B)`.
    have h₁ : interior A ⊆ interior (A ∪ B) := by
      apply interior_mono
      intro y hy
      exact Or.inl hy
    -- Then take closures.
    have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono h₁
    -- Finally, take interiors once more.
    exact interior_mono h₂
  -- Split on whether `x` comes from `A` or `B`.
  cases hx with
  | inl hxA =>
      have hxInt : x ∈ interior (closure (interior A)) := hA hxA
      exact hsubset hxInt
  | inr hxB =>
      have hxInt : x ∈ interior (closure (interior A)) := hB hxB
      exact hsubset hxInt

theorem Topology.closure_interior_closure_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure A))) = closure (interior (closure A)) := by
  simpa [closure_closure] using
    (rfl :
      closure (interior (closure (closure A))) =
        closure (interior (closure (closure A))))

theorem Topology.isClosed_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior (closure A))) := by
  simpa using (isClosed_closure (s := interior (closure A)))

theorem Topology.interior_closure_eq_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = interior (closure (interior (closure A))) := by
  apply Set.Subset.antisymm
  ·
    -- `interior (closure A)` is open and contained in `closure (interior (closure A))`.
    have hsubset : interior (closure A) ⊆ closure (interior (closure A)) := by
      intro x hx
      exact subset_closure hx
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    -- Hence it is contained in the interior of that closure.
    exact interior_maximal hsubset hOpen
  ·
    -- Use the previously established inclusion for the reverse direction.
    have hsubset :
        interior (closure (interior (closure A))) ⊆
          interior (closure (closure A)) :=
      interior_closure_interior_subset_interior_closure (A := closure A)
    -- Simplify with the equality `interior (closure (closure A)) = interior (closure A)`.
    simpa [Topology.interior_closure_closure_eq_interior_closure (A := A)] using hsubset

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  simpa using (Topology.P1_closure_interior (A := closure A))

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro hA
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := (hA A hA_mem) hxA
  -- We show that this interior is contained in the desired one.
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- Step 1: `interior A ⊆ interior (⋃₀ 𝒜)`
    have h₁ : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    have h₂ : interior A ⊆ interior (⋃₀ 𝒜) := interior_mono h₁
    -- Step 2: take closures
    have h₃ : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h₂
    -- Step 3: take interiors again
    exact interior_mono h₃
  exact hsubset hxInt

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_closure : x ∈ closure (interior A) := (hA A hA_mem) hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    apply closure_mono
    have : interior A ⊆ interior (⋃₀ 𝒜) := by
      apply interior_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact this
  exact hsubset hx_closure

theorem Topology.P2_of_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A → Topology.P2 A := by
  intro hP3
  -- From `P3` and closedness we deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  -- Every open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A) hOpen

theorem Topology.P1_of_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  -- From `P2` and closedness, we deduce that `A` is open.
  have hOpen : IsOpen A := Topology.isOpen_of_P2_of_isClosed (A := A) hA hP2
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A) hOpen

theorem Topology.P3_closure_closure_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P3 (closure A) := by
  have hEq : closure (closure A) = closure A := closure_closure
  constructor
  · intro hP3
    simpa [hEq] using hP3
  · intro hP3
    simpa [hEq] using hP3

theorem Topology.interior_closure_eq_of_isClosed_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    interior (closure A) = A := by
  simpa [hA_closed.closure_eq, hA_open.interior_eq]

theorem Topology.interior_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure (A ∩ B)` is contained in each individual closure.
  have hA : closure (A ∩ B) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  have hB : closure (A ∩ B) ⊆ closure B := by
    apply closure_mono
    intro y hy
    exact hy.2
  -- Use monotonicity of `interior` to upgrade the membership.
  have hxA : x ∈ interior (closure A) := (interior_mono hA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono hB) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono h)

theorem Topology.interior_closure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hxA
  | inr hxB =>
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_right
        exact this
      exact hsubset hxB

theorem Topology.interior_closure_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  -- The set difference `A \ B` is clearly a subset of `A`.
  have hsubset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Apply the monotonicity of `interior ∘ closure`.
  exact Topology.interior_closure_mono (A := A \ B) (B := A) hsubset

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- Step 1: from `A ⊆ B` deduce `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono h
  -- Step 2: take closures to obtain `closure (interior A) ⊆ closure (interior B)`.
  have hCl : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  -- Step 3: apply `interior` once more, using its monotonicity.
  exact interior_mono hCl

theorem Topology.closure_interior_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior (closure A))) = closure (interior (closure A)) := by
  simpa [interior_interior]

theorem Topology.P1_and_P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P3 A) ↔ IsOpen A := by
  -- `P3 A` is equivalent to `IsOpen A` for closed sets.
  have hP3 : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (A := A) hA
  -- Establish the desired equivalence.
  constructor
  · rintro ⟨_, hPA3⟩
    -- From the second component obtain openness.
    exact hP3.1 hPA3
  · intro hOpen
    -- Openness yields both `P1` and `P3`.
    exact
      And.intro
        (Topology.P1_of_isOpen (A := A) hOpen)
        (Topology.P3_of_isOpen (A := A) hOpen)

theorem Topology.dense_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    simpa [hDense.closure_eq, interior_univ]
  · intro hInt
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x hx
      have hxInt : x ∈ interior (closure A) := by
        simpa [hInt] using hx
      exact (interior_subset : interior (closure A) ⊆ closure A) hxInt
    have h_closure_eq : closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; simp
      · exact h_subset
    simpa using (dense_iff_closure_eq).2 h_closure_eq

theorem Topology.closure_interior_eq_of_isClosed_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    closure (interior A) = A := by
  -- The interior of an open set is itself.
  have hInt : interior A = A := hA_open.interior_eq
  -- The closure of a closed set is itself.
  have hCl : closure A = A := hA_closed.closure_eq
  -- Combine the two equalities to obtain the result.
  simpa [hInt, hCl]

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
      simpa using
        (Topology.closure_interior_closure_interior_eq_closure_interior
          (A := closure (interior A)))
    _ = closure (interior A) := by
      simpa using
        (Topology.closure_interior_closure_interior_eq_closure_interior
          (A := A))

theorem Topology.interior_eq_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  have hOpen : IsOpen A :=
    Topology.isOpen_of_P2_of_isClosed (A := A) hA hP2
  simpa using hOpen.interior_eq

theorem Topology.interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) :
    interior (closure A) = (Set.univ : Set X) := by
  have hclosure : closure A = (Set.univ : Set X) := by
    simpa using h.closure_eq
  simpa [hclosure, interior_univ]

theorem Topology.P3_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (closure A) := by
  intro hDense
  have hEq : closure (closure A) = (Set.univ : Set X) := by
    simpa [closure_closure] using hDense.closure_eq
  simpa using
    (Topology.P3_of_closure_eq_univ (A := closure A) hEq)



theorem Topology.closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- First inclusion: `closure (interior (A ∩ B)) ⊆ closure (interior A)`
  have hA : closure (interior (A ∩ B)) ⊆ closure (interior A) := by
    -- Since `A ∩ B ⊆ A`, we get `interior (A ∩ B) ⊆ interior A`.
    have hinner : interior (A ∩ B) ⊆ interior A := by
      have hsubset : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact interior_mono hsubset
    -- Taking closures preserves inclusion.
    exact closure_mono hinner
  -- Second inclusion: `closure (interior (A ∩ B)) ⊆ closure (interior B)`
  have hB : closure (interior (A ∩ B)) ⊆ closure (interior B) := by
    -- Since `A ∩ B ⊆ B`, we get `interior (A ∩ B) ⊆ interior B`.
    have hinner : interior (A ∩ B) ⊆ interior B := by
      have hsubset : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact interior_mono hsubset
    -- Taking closures preserves inclusion.
    exact closure_mono hinner
  exact And.intro (hA hx) (hB hx)

theorem Topology.interior_closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  have h : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    have hsubset : closure (⋂ j, A j) ⊆ closure (A i) := by
      apply closure_mono
      exact Set.iInter_subset _ i
    have hsubset_int :
        interior (closure (⋂ j, A j)) ⊆ interior (closure (A i)) :=
      interior_mono hsubset
    exact hsubset_int hx
  exact Set.mem_iInter.2 h

theorem Topology.closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hsubset hxA
  | inr hxB =>
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact hsubset hxB

theorem Topology.P1_of_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- `x` is in `closure (interior A)` by assumption.
  have hxA : x ∈ closure (interior A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves this inclusion.
  have hCl : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  -- Conclude the desired membership.
  exact hCl hxA

theorem Topology.P1_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P1 (closure A) := by
  intro hDense
  have hEq : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [hEq] using (P1_univ (X := X))

theorem Topology.closed_dense_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Dense A → (A : Set X) = Set.univ := by
  intro hClosed hDense
  have h1 : closure A = A := hClosed.closure_eq
  have h2 : closure A = (Set.univ : Set X) := hDense.closure_eq
  simpa [h1] using h2

theorem Topology.interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A := by
    have hsub : (A ∩ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact (interior_mono hsub) hx
  have hxB : x ∈ interior B := by
    have hsub : (A ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact (interior_mono hsub) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  simpa using
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A))

theorem Topology.interior_closure_eq_of_isClosed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    interior (closure A) = A := by
  -- From `P3` and closedness we get that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.isOpen_of_P3_of_isClosed (A := A) hA_closed) hP3
  -- The interior of an open set is itself.
  have hInt : interior A = A := hOpen.interior_eq
  -- The closure of a closed set is itself.
  have hCl : closure A = A := hA_closed.closure_eq
  -- Combine the two equalities.
  simpa [hCl, hInt]

theorem Topology.closure_interior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (interior (⋂ i, A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  have h : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    have hsubset_inner : interior (⋂ j, A j) ⊆ interior (A i) := by
      have hbase : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ i
      exact interior_mono hbase
    have hsubset_closure :
        closure (interior (⋂ j, A j)) ⊆ closure (interior (A i)) :=
      closure_mono hsubset_inner
    exact hsubset_closure hx
  exact Set.mem_iInter.2 h

theorem Topology.P1_P2_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    (Topology.P1 A) ∧ (Topology.P2 A) ∧ (Topology.P3 A) := by
  exact
    And.intro
      (Topology.P1_of_isOpen (A := A) hA)
      (And.intro
        (Topology.P2_of_isOpen (A := A) hA)
        (Topology.P3_of_isOpen (A := A) hA))

theorem Topology.P1_P2_P3_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_dense_interior (A := A) hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_dense_interior (A := A) hDense
  have hP3 : Topology.P3 A :=
    Topology.P3_of_dense_interior (A := A) hDense
  exact And.intro hP1 (And.intro hP2 hP3)

theorem Topology.P2_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  -- Every open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := Aᶜ) hOpen

theorem Topology.P2_closure_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P2 (closure A) := by
  intro hP3
  -- Since `closure A` is closed, `P3` implies it is open.
  have hOpen : IsOpen (closure A) := by
    have hClosed : IsClosed (closure A) := isClosed_closure
    exact (Topology.isOpen_of_P3_of_isClosed (A := closure A) hClosed) hP3
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := closure A) hOpen

theorem Topology.interior_closure_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  exact
    (interior_mono (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))) hx

theorem Topology.P2_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P2 (closure A) := by
  intro hDense
  -- Since `A` is dense, its closure is the whole space.
  have hEq : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Rewriting with `hEq`, the statement reduces to `P2` for `Set.univ`,
  -- which is already established.
  simpa [hEq] using (P2_univ (X := X))

theorem Topology.isClosed_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior A)) := by
  simpa using (isClosed_closure (s := interior A))

theorem Topology.P3_closure_interior_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure (interior A)) := by
  intro hDense
  -- Since `interior A` is dense, its (double) closure is the whole space.
  have hEq : closure (closure (interior A)) = (Set.univ : Set X) := by
    simpa [closure_closure] using hDense.closure_eq
  -- Apply the existing lemma to conclude the `P3` property.
  exact Topology.P3_of_closure_eq_univ (A := closure (interior A)) hEq

theorem Topology.P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  -- Every open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := Aᶜ) hOpen

theorem Topology.P1_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := Aᶜ) hOpen

theorem Topology.interior_closure_interior_eq_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    interior (closure (interior A)) = interior (closure A) := by
  simpa [hA.interior_eq]

theorem Topology.P2_closure_interior_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 (closure (interior A)) := by
  intro hDense
  -- Since `interior A` is dense, its closure is the whole space.
  have hEq : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Rewriting with `hEq`, the statement reduces to `P2` for `Set.univ`,
  -- which is already established.
  simpa [hEq] using (P2_univ (X := X))

theorem Topology.interior_closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Inclusion related to `A`.
  have hA_sub : (A ∩ B : Set X) ⊆ A := by
    intro y hy; exact hy.1
  have hA_int : interior (A ∩ B) ⊆ interior A := interior_mono hA_sub
  have hA_cl : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono hA_int
  have hxA : x ∈ interior (closure (interior A)) :=
    (interior_mono hA_cl) hx
  -- Inclusion related to `B`.
  have hB_sub : (A ∩ B : Set X) ⊆ B := by
    intro y hy; exact hy.2
  have hB_int : interior (A ∩ B) ⊆ interior B := interior_mono hB_sub
  have hB_cl : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono hB_int
  have hxB : x ∈ interior (closure (interior B)) :=
    (interior_mono hB_cl) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  -- First inclusion: `⊆`
  apply Set.Subset.antisymm
  ·
    have h :=
      interior_closure_interior_subset_interior_closure (A := closure A)
    simpa [closure_closure] using h
  ·
    -- Second inclusion: `⊇`
    intro x hx
    -- `interior (closure A)` is open.
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    -- It is contained in its own closure.
    have hsubset : (interior (closure A) : Set X) ⊆
        closure (interior (closure A)) := by
      intro y hy
      exact subset_closure hy
    -- Hence it is contained in the interior of that closure.
    have h' : (interior (closure A) : Set X) ⊆
        interior (closure (interior (closure A))) :=
      interior_maximal hsubset hOpen
    exact h' hx

theorem Topology.interior_closure_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA.closure_eq]

theorem Topology.dense_interior_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ interior (closure (interior A)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    have hcl : closure (interior A) = (Set.univ : Set X) := by
      simpa using hDense.closure_eq
    simpa [hcl, interior_univ]
  · intro hIntEq
    -- First, show that `closure (interior A)` is the whole space.
    have hsubset : (Set.univ : Set X) ⊆ closure (interior A) := by
      intro x _
      have hx : x ∈ interior (closure (interior A)) := by
        simpa [hIntEq]
      exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx
    have hcl : closure (interior A) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; simp
      · exact hsubset
    -- Conclude density from the equality of closures.
    exact (dense_iff_closure_eq).2 hcl



theorem interior_union
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (A ∪ B : Set X) = interior (A ∪ B) :=
  rfl

theorem Topology.P2_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P2 (closure A) := by
  exact Topology.P2_of_isOpen (A := closure A) hOpen

theorem Topology.closure_interior_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.interior_union_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have hInt : interior A ⊆ interior (A ∪ B) := interior_mono hsubset
      exact hInt hA
  | inr hB =>
      have hsubset : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hInt : interior B ⊆ interior (A ∪ B) := interior_mono hsubset
      exact hInt hB

theorem Topology.interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  -- The set `interior A` is contained in its closure.
  have hsubset : (interior A : Set X) ⊆ closure (interior A) := by
    intro x hx
    exact subset_closure hx
  -- Apply the monotonicity of `interior`.
  have hmono : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono hsubset
  simpa [interior_interior] using hmono

theorem Topology.P1_closure_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure (closure A)) := by
  intro hP1
  have h : Topology.P1 (closure A) := Topology.P1_closure (A := A) hP1
  simpa [closure_closure] using h

theorem Topology.P1_of_between
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- From the assumption `B ⊆ closure (interior A)` we get
  -- that `x` lies in `closure (interior A)`.
  have hx_closureA : x ∈ closure (interior A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusion.
  have hCl : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Conclude that `x` lies in `closure (interior B)`.
  exact hCl hx_closureA

theorem Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  -- First contraction using idempotence of `interior ∘ closure`.
  have h₁ :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure
        (A := interior (closure A)))
  -- Second contraction to reach the final form.
  have h₂ :
      interior (closure (interior (closure A))) = interior (closure A) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure (A := A))
  simpa [h₁, h₂]

theorem Topology.interior_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (A : ι → Set X) :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hsubset : interior (A i) ⊆ interior (⋃ i, A i) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hsubset hxi

theorem Topology.dense_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense A := by
  intro hDenseInt
  -- `closure (interior A)` is the whole space.
  have hIntUniv : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDenseInt.closure_eq
  -- Monotonicity of `closure` gives a useful inclusion.
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Show that `closure A` is also the whole space.
  have hAUniv : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; simp
    · intro x _
      have hx : x ∈ closure (interior A) := by
        simpa [hIntUniv] using (by simp : x ∈ (Set.univ : Set X))
      exact hsubset hx
  -- Conclude density from the closure equality.
  simpa using (dense_iff_closure_eq).2 hAUniv

theorem Topology.closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  -- Since `A` is dense, its closure is the whole space.
  have hclosure : closure A = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Rewriting with this equality simplifies the goal to a tautology.
  simpa [hclosure, interior_univ, closure_univ]

theorem Topology.interior_closure_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (closure (A i))) ⊆ interior (closure (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  -- Show `closure (A i)` is contained in `closure (⋃ i, A i)`.
  have hsubset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Monotonicity of `interior` then yields the desired inclusion.
  have hIntSubset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono hsubset
  exact hIntSubset hxInt



theorem Topology.P2_iff_P3_and_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P3 A ∧ closure A = closure (interior A)) := by
  -- First, express `P2` in terms of `P1` and `P3`.
  have h1 : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) :=
    Topology.P2_iff_P1_and_P3 (A := A)
  -- Next, replace `P1` by the closure equality using the existing equivalence.
  have h2 : Topology.P1 A ↔ closure A = closure (interior A) :=
    Topology.P1_iff_closure_eq_closure_interior (A := A)
  have h3 :
      (Topology.P1 A ∧ Topology.P3 A) ↔
        (closure A = closure (interior A) ∧ Topology.P3 A) := by
    simpa using (and_congr h2 (Iff.rfl))
  -- Finally, reorder the conjuncts to match the desired statement.
  have h4 :
      (closure A = closure (interior A) ∧ Topology.P3 A) ↔
        (Topology.P3 A ∧ closure A = closure (interior A)) := by
    constructor
    · intro h; exact And.symm h
    · intro h; exact And.symm h
  -- Chain the equivalences.
  simpa using h1.trans (h3.trans h4)

theorem Topology.interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure (interior A))`.
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        -- Show `closure (interior A) ⊆ closure (interior (A ∪ B))`.
        have hcl : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          -- Show `interior A ⊆ interior (A ∪ B)`.
          have : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact this
        exact hcl
      exact hsubset hxA
  | inr hxB =>
      -- Handle the case `x ∈ interior (closure (interior B))`.
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        -- Show `closure (interior B) ⊆ closure (interior (A ∪ B))`.
        have hcl : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          -- Show `interior B ⊆ interior (A ∪ B)`.
          have : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact this
        exact hcl
      exact hsubset hxB

theorem Topology.interior_closure_interior_univ_eq_univ
    {X : Type*} [TopologicalSpace X] :
    interior (closure (interior (Set.univ : Set X))) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]

theorem Topology.interior_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior (closure A)) = interior (closure A) := by
  simpa [interior_interior]

theorem Topology.interior_closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Membership in `interior (closure A)`
  have hA : closure (A ∩ interior B) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  have hxA : x ∈ interior (closure A) := (interior_mono hA) hx
  -- Membership in `interior (closure B)`
  have hB : closure (A ∩ interior B) ⊆ closure B := by
    -- Since `interior B ⊆ B`, the desired inclusion follows.
    have hsub : (A ∩ interior B : Set X) ⊆ B := by
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact closure_mono hsub
  have hxB : x ∈ interior (closure B) := (interior_mono hB) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_subset_interior_closure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  -- `closure B` is contained in `closure (A ∪ B)`.
  have hsubset : closure B ⊆ closure (A ∪ B) := by
    apply closure_mono
    exact Set.subset_union_right
  -- Monotonicity of `interior` gives the desired inclusion.
  exact (interior_mono hsubset) hx

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact closure_mono h

theorem Topology.closure_interior_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simpa [interior_empty] using
    (closure_empty : closure (∅ : Set X) = (∅ : Set X))

theorem interior_closure_univ_eq_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simp [closure_univ, interior_univ]

theorem Topology.P3_iff_P1_and_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalences for open sets.
  have h1 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  have h2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  -- Prove each direction of the desired equivalence.
  constructor
  · intro hP3
    -- Obtain `P1` from `P3` using `h1`.
    have hP1 : Topology.P1 A := (h1.symm).mp hP3
    -- Obtain `P2` from `P1` using `h2`.
    have hP2 : Topology.P2 A := h2.mp hP1
    exact And.intro hP1 hP2
  · rintro ⟨hP1, _⟩
    -- Derive `P3` from `P1` using `h1`.
    exact h1.mp hP1



theorem Topology.P1_iff_P2_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3
  · intro hP2
    exact P2_implies_P1 (A := A) hP2

theorem Topology.P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact P2_implies_P3 (A := A) hP2
  · intro hP3
    exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3

theorem Topology.closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- `interior (closure A)` is contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusion.
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h₂

theorem Topology.P2_compl_iff_P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  -- Apply the existing equivalence for open sets.
  simpa using (Topology.P2_iff_P3_of_isOpen (A := Aᶜ) hOpen)

theorem Topology.eq_empty_of_P2_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = ∅) (hP2 : Topology.P2 A) :
    (A : Set X) = ∅ := by
  -- First, show `A ⊆ ∅`.
  have hsubset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    -- From `P2`, we know `x` lies in the specified interior.
    have hx' : x ∈ interior (closure (interior A)) := hP2 hx
    -- But that interior is empty, thanks to `hInt`.
    have hEmpty : interior (closure (interior A)) = (∅ : Set X) := by
      simp [hInt]
    -- Hence `x` belongs to the empty set, an impossibility.
    have : x ∈ (∅ : Set X) := by
      simpa [hEmpty] using hx'
    exact this.elim
  -- Conclude the desired equality of sets.
  exact Set.Subset.antisymm hsubset (Set.empty_subset _)

theorem Topology.P1_compl_iff_P2_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  -- Apply the existing equivalence for open sets.
  simpa using (Topology.P1_iff_P2_of_isOpen (A := Aᶜ) hOpen)

theorem Topology.interior_closure_union_eq_interior_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  -- First, `interior S ⊆ closure S` for any set `S`.
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- Second, we already have `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  -- Compose the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem Topology.closure_interior_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (interior (A i)) : Set X) ⊆
      closure (interior (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hsubset : closure (interior (A i)) ⊆
      closure (interior (⋃ j, A j)) := by
    apply closure_mono
    have : interior (A i) ⊆ interior (⋃ j, A j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hsubset hxAi

theorem Topology.closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  -- `interior A` is contained in `A`.
  have h : interior A ⊆ (A : Set X) := interior_subset
  -- Taking closures preserves inclusion.
  exact closure_mono h

theorem Topology.interior_union_eq_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  simpa using hOpen.interior_eq

theorem Topology.P1_compl_iff_P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is an open set.
  have hOpen : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  -- For open sets, `P1` and `P3` are equivalent.
  simpa using (Topology.P1_iff_P3_of_isOpen (A := Aᶜ) hOpen)

theorem Topology.interior_inter_eq_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B : Set X) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using hOpen.interior_eq

theorem Topology.P1_and_P2_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A) ↔ IsOpen A := by
  -- Existing equivalence between `P2` and openness for closed sets.
  have hEq : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (A := A) hA
  -- Prove each direction.
  constructor
  · rintro ⟨_, hP2⟩
    exact hEq.mp hP2
  · intro hOpen
    exact And.intro
      (Topology.P1_of_isOpen (A := A) hOpen)
      (hEq.mpr hOpen)

theorem Topology.interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact (subset_closure : interior (closure A) ⊆ closure (interior (closure A))) hx

theorem Topology.P2_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (closure A) → Topology.P2 (closure B) → Topology.P2 (closure A ∪ closure B) := by
  intro hA hB
  simpa using (Topology.P2_union (A := closure A) (B := closure B) hA hB)

theorem Topology.closure_interior_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ⊆ closure B := by
  -- Since `interior A ⊆ A` and `A ⊆ B`, we get `interior A ⊆ B`.
  have hsubset : (interior A : Set X) ⊆ B :=
    Set.Subset.trans (interior_subset : (interior A : Set X) ⊆ A) hAB
  -- Taking closures preserves set inclusion.
  exact closure_mono hsubset

theorem Topology.isClopen_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 A) : IsClopen A := by
  have hOpen : IsOpen A :=
    Topology.isOpen_of_P2_of_isClosed (A := A) hClosed hP2
  exact ⟨hClosed, hOpen⟩

theorem Topology.P2_iff_P3_and_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      (Topology.P3 A ∧ interior (closure A) = interior (closure (interior A))) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := P2_implies_P3 (A := A) hP2
    have hEq : interior (closure A) = interior (closure (interior A)) :=
      Topology.interior_closure_eq_interior_closure_interior_of_P2 (A := A) hP2
    exact And.intro hP3 hEq
  · rintro ⟨hP3, hEq⟩
    exact
      Topology.P2_of_P3_and_interior_closure_eq
        (A := A) hP3 hEq

theorem Topology.closure_interior_subset_closure_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ⊆ closure (interior (A ∪ B)) := by
  -- Since `A ⊆ A ∪ B`, the corresponding interiors satisfy the same inclusion.
  have hInt : interior A ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inl hx
  -- Taking closures preserves inclusions.
  exact closure_mono hInt

theorem Topology.closure_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem Topology.P2_iff_isClopen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 A ↔ IsClopen A := by
  constructor
  · intro hP2
    have hOpen : IsOpen A :=
      Topology.isOpen_of_P2_of_isClosed (A := A) hA hP2
    exact ⟨hA, hOpen⟩
  · intro hClopen
    exact Topology.P2_of_isOpen (A := A) hClopen.2

theorem P2_iff_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P2_iff_P3_of_isOpen (A := interior A) hOpen)

theorem Topology.P1_iff_P3_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ↔ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A := P2_implies_P1 (A := A) hP2
  have hP3 : Topology.P3 A := P2_implies_P3 (A := A) hP2
  exact ⟨fun _ => hP3, fun _ => hP1⟩

theorem Topology.dense_closure_iff_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure A) ↔ Dense A := by
  constructor
  · intro hDenseCl
    -- `Dense (closure A)` gives `closure (closure A) = univ`.
    have hEq : closure (closure A) = (Set.univ : Set X) := hDenseCl.closure_eq
    -- Use idempotence of `closure` to simplify.
    have hEq' : closure A = (Set.univ : Set X) := by
      simpa [closure_closure] using hEq
    -- Conclude that `A` is dense.
    exact (dense_iff_closure_eq).2 hEq'
  · intro hDenseA
    -- `Dense A` yields `closure A = univ`.
    have hEq : closure A = (Set.univ : Set X) := hDenseA.closure_eq
    -- Therefore `closure (closure A) = univ`.
    have hEq' : closure (closure A) = (Set.univ : Set X) := by
      simpa [closure_closure, hEq, closure_univ]
    -- Conclude that `closure A` is dense.
    exact (dense_iff_closure_eq).2 hEq'

theorem Topology.P1_P2_P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A := by
  constructor
  · rintro ⟨_, _, hP3⟩
    exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  · intro hOpen
    exact
      And.intro
        (Topology.P1_of_isOpen (A := A) hOpen)
        (And.intro
          (Topology.P2_of_isOpen (A := A) hOpen)
          (Topology.P3_of_isOpen (A := A) hOpen))

theorem Topology.closure_interior_union_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B : Set X) ⊆
      closure (interior (A ∪ B)) := by
  -- First, show that `interior A ∪ interior B` is contained in `interior (A ∪ B)`.
  have hsubset : (interior A ∪ interior B : Set X) ⊆ interior (A ∪ B) := by
    intro x hx
    cases hx with
    | inl hA =>
        have hA' : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact hA' hA
    | inr hB =>
        have hB' : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact hB' hB
  -- Taking closures preserves inclusions.
  exact closure_mono hsubset

theorem Topology.closure_interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  -- Since `A \ B ⊆ A`, the same inclusion holds for their interiors.
  have hsubset : interior (A \ B) ⊆ interior A := by
    have hAB : (A \ B : Set X) ⊆ A := by
      intro x hx
      exact hx.1
    exact interior_mono hAB
  -- Taking closures preserves set inclusion.
  exact closure_mono hsubset

theorem Topology.interior_union_interior_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (interior A ∪ interior B) = interior A ∪ interior B := by
  -- `interior A` and `interior B` are open, hence their union is open.
  have hOpen : IsOpen ((interior A ∪ interior B) : Set X) := by
    exact (isOpen_interior.union isOpen_interior)
  -- For an open set `S`, we have `interior S = S`.
  simpa [hOpen.interior_eq]

theorem Topology.P2_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior (A ∪ B)) := by
  -- The set `interior (A ∪ B)` is open.
  have hOpen : IsOpen (interior (A ∪ B)) := isOpen_interior
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := interior (A ∪ B)) hOpen

theorem P3_iff_isClopen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A ↔ IsClopen A := by
  -- For closed sets, `P3 A` is equivalent to `IsOpen A`.
  have hOpen : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (A := A) hA
  constructor
  · intro hP3
    -- From `P3` obtain openness, then combine with closedness.
    have hA_open : IsOpen A := hOpen.mp hP3
    exact ⟨hA, hA_open⟩
  · intro hClopen
    -- Openness of `A` implies `P3 A`.
    exact Topology.P3_of_isOpen (A := A) hClopen.2

theorem Topology.P3_of_P2_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A → Topology.P3 A := by
  intro hP2
  -- From `P2` and closedness we deduce that `A` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_P2_of_isClosed (A := A) hA hP2
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A) hOpen

theorem Topology.subset_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior (closure A)) := by
  intro hP1
  -- Step 1: from `P1`, we have `A ⊆ closure (interior A)`.
  have h₁ : (A : Set X) ⊆ closure (interior A) := hP1
  -- Step 2: `interior A ⊆ interior (closure A)` by monotonicity.
  have hInt : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Step 3: taking closures preserves the inclusion.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono hInt
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem Topology.P1_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior (A ∪ B)) := by
  -- The set `interior (A ∪ B)` is open, hence it satisfies `P1`.
  have hOpen : IsOpen (interior (A ∪ B)) := isOpen_interior
  exact Topology.P1_of_isOpen (A := interior (A ∪ B)) hOpen

theorem Topology.interior_closure_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure A ∩ closure B ⊆ closure A`
  have hsubA : closure A ∩ closure B ⊆ closure A := by
    intro y hy
    exact hy.1
  -- `closure A ∩ closure B ⊆ closure B`
  have hsubB : closure A ∩ closure B ⊆ closure B := by
    intro y hy
    exact hy.2
  -- Use monotonicity of `interior` to upgrade the membership.
  have hxA : x ∈ interior (closure A) := (interior_mono hsubA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono hsubB) hx
  exact And.intro hxA hxB

theorem Topology.P3_of_between
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure A)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  -- Step 1: upgrade `x ∈ B` to `x ∈ interior (closure A)`.
  have hxIntA : x ∈ interior (closure A) := hBsubset hxB
  -- Step 2: use monotonicity of `closure` and `interior` to reach `closure B`.
  have hclosure : closure A ⊆ closure B := closure_mono hAB
  have hIntMono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono hclosure
  exact hIntMono hxIntA



theorem Topology.P2_of_between
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P2 B := by
  dsimp [Topology.P2] at *
  intro x hxB
  -- Step 1: upgrade `x ∈ B` to `x ∈ interior (closure (interior A))`.
  have hxIntA : x ∈ interior (closure (interior A)) := hBsubset hxB
  -- Step 2: use monotonicity of `interior ∘ closure ∘ interior`
  -- with the inclusion `A ⊆ B`.
  have hmono :
      interior (closure (interior A)) ⊆
        interior (closure (interior B)) :=
    Topology.interior_closure_interior_mono (A := A) (B := B) hAB
  exact hmono hxIntA

theorem Topology.closure_interior_closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- First, rewrite the interiors of the two closures using `P2`.
  have hInt :
      interior (closure A) = interior (closure (interior A)) :=
    Topology.interior_closure_eq_interior_closure_interior_of_P2 (A := A) hP2
  -- Taking closures of both sides preserves the equality.
  have hCl :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) := by
    simpa using congrArg (fun S : Set X => closure S) hInt
  -- Use the idempotence lemma to finish.
  calc
    closure (interior (closure A))
        = closure (interior (closure (interior A))) := hCl
    _ = closure (interior A) :=
      (Topology.closure_interior_closure_interior_eq_closure_interior (A := A))



theorem Topology.P3_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (closure A) → Topology.P3 (closure B) → Topology.P3 (closure A ∪ closure B) := by
  intro hA hB
  simpa using (Topology.P3_union (A := closure A) (B := closure B) hA hB)

theorem Topology.P1_P2_P3_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  intro hClopen
  have hOpen : IsOpen A := hClopen.2
  exact Topology.P1_P2_P3_of_isOpen (A := A) hOpen

theorem Topology.closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in its closure, which is empty by assumption.
    have hsubset : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ closure (interior A) := subset_closure hx
      simpa [h] using this
    -- Conclude that `interior A` itself is empty.
    exact Set.Subset.antisymm hsubset (Set.empty_subset _)
  · intro hInt
    -- Rewriting with `hInt` reduces the goal to `closure ∅ = ∅`.
    simpa [hInt, closure_empty]

theorem Topology.isClosed_of_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (A : Set X)) :
    IsClosed A := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa [h] using hClosed

theorem Topology.closure_interior_subset_closure_interior_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  -- Since `B ⊆ A ∪ B`, the corresponding interiors satisfy the same inclusion.
  have hInt : interior B ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inr hx
  -- Taking closures preserves inclusions.
  exact closure_mono hInt

theorem Topology.closure_interior_closure_interior_closure_interior_closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, shorten the goal using the existing 3-fold contraction lemma
  have h1 :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior
        (A := closure (interior A)))
  -- Next, contract once more using the 2-fold lemma
  have h2 :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior (A := A))
  -- Combine the two equalities to obtain the desired result
  simpa [h2] using h1

theorem Topology.P3_union_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Dense A) :
    Topology.P3 (A ∪ B) := by
  -- `A` itself satisfies `P3`.
  have hP3A : Topology.P3 A := Topology.P3_of_dense (A := A) hA
  -- Since `A` is dense, `interior (closure A)` is the whole space.
  have hClosure : closure A = (Set.univ : Set X) := hA.closure_eq
  -- Hence every element of `B` lies in `interior (closure A)`.
  have hsubset : (B : Set X) ⊆ interior (closure A) := by
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hClosure, interior_univ] using this
  -- Apply the existing union lemma.
  exact Topology.P3_union_of_subset (A := A) (B := B) hP3A hsubset

theorem Topology.isClopen_of_isClosed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsClopen A := by
  -- From `P3` and closedness we obtain that `A` is open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3
  exact ⟨hA_closed, hA_open⟩

theorem Topology.P2_iff_P3_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure A = closure (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- `P2 A` is equivalent to `P3 A ∧ closure A = closure (interior A)`.
  have h := Topology.P2_iff_P3_and_closure_eq_closure_interior (A := A)
  constructor
  · intro hP2
    exact (h.mp hP2).1
  · intro hP3
    exact
      Topology.P2_of_P3_and_closure_eq_closure_interior
        (A := A) hP3 hEq

theorem Topology.closure_interior_inter_subset_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A ∩ interior B) := by
  -- Start with the inclusion between the interiors.
  have hsubset : interior (A ∩ B) ⊆ interior A ∩ interior B :=
    Topology.interior_inter_subset (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono hsubset

theorem interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty, interior_empty]

theorem Topology.closure_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A := by
  -- The set `A ∩ B` is contained in `A`.
  have h : (A ∩ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h

theorem Topology.P1_compl_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ IsOpen (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  constructor
  · intro _; exact hOpen
  · intro hOpenCompl
    exact Topology.P1_of_isOpen (A := Aᶜ) hOpenCompl

theorem Topology.dense_interior_union_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : Dense (interior A)) : Dense (interior (A ∪ B)) := by
  -- From density obtain the closure equality for `interior A`.
  have hClosureA : closure (interior A) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- `interior A` is contained in `interior (A ∪ B)`.
  have hSubsetInt : interior A ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inl hx
  -- Therefore the corresponding closures satisfy the same inclusion.
  have hSubsetCl :
      closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono hSubsetInt
  -- Combine with `hClosureA` to see that the latter closure is the whole space.
  have hEq : closure (interior (A ∪ B)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; simp
    · simpa [hClosureA] using hSubsetCl
  -- Conclude density from the closure equality.
  exact (dense_iff_closure_eq).2 hEq

theorem Topology.P2_iff_P3_of_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure A) = interior (closure (interior A))) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    -- Extract `P3 A` from the existing equivalence.
    have h := (Topology.P2_iff_P3_and_interior_closure_eq (A := A)).1 hP2
    exact h.1
  · intro hP3
    -- Build `P2 A` using the provided equality.
    exact
      Topology.P2_of_P3_and_interior_closure_eq
        (A := A) hP3 hEq

theorem Topology.isOpen_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → IsOpen (closure A) := by
  intro hDense
  have hEq : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDense
  simpa [hEq] using isOpen_univ

theorem Topology.closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each `i`, `(⋂ j, A j) ⊆ A i`, so their closures satisfy the same inclusion.
  have h : ∀ i, x ∈ closure (A i) := by
    intro i
    have hsubset : (⋂ j, A j : Set X) ⊆ A i := by
      exact Set.iInter_subset _ i
    have : closure (⋂ j, A j) ⊆ closure (A i) := closure_mono hsubset
    exact this hx
  -- Combine the individual memberships into one for the intersection of closures.
  exact Set.mem_iInter.2 h

theorem Topology.closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : closure (interior A) ⊆ (A : Set X) := by
  -- `interior A` is contained in `A`.
  have hsubset : (interior A : Set X) ⊆ A := interior_subset
  -- Taking closures preserves inclusion.
  have hclosure : closure (interior A) ⊆ closure A := closure_mono hsubset
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using hclosure

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `A ∩ B` is contained in `A`, hence its closure is contained in `closure A`.
  have hA : (A ∩ B : Set X) ⊆ A := by
    intro y hy; exact hy.1
  have hxA : x ∈ closure A := (closure_mono hA) hx
  -- Similarly for `B`.
  have hB : (A ∩ B : Set X) ⊆ B := by
    intro y hy; exact hy.2
  have hxB : x ∈ closure B := (closure_mono hB) hx
  exact And.intro hxA hxB

theorem Topology.P2_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P2 A := by
  intro hClopen
  exact Topology.P2_of_isOpen (A := A) hClopen.2

theorem Topology.P2_iff_P1_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) :
    Topology.P2 A ↔ Topology.P1 A := by
  simpa using
    (Topology.P1_iff_P2_of_isOpen (A := A) hA.2).symm

theorem Topology.closure_interior_eq_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) :
    closure (interior A) = closure A := by
  have h₁ : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  have h₂ : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) h
  simpa [h₁, h₂]

theorem Topology.P1_iff_P2_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P1_iff_P2_of_isOpen (A := interior A) hOpen)



theorem Topology.P2_inter_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (closure A) → Topology.P2 (closure B) → Topology.P2 (closure A ∩ closure B) := by
  intro hA hB
  have hA_closed : IsClosed (closure A) := isClosed_closure
  have hB_closed : IsClosed (closure B) := isClosed_closure
  exact
    Topology.P2_inter
      (A := closure A) (B := closure B)
      hA_closed hB_closed
      hA hB

theorem Topology.P1_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P1 A := by
  intro hClopen
  exact Topology.P1_of_isOpen (A := A) hClopen.2

theorem Topology.P3_iff_P1_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) :
    Topology.P3 A ↔ Topology.P1 A := by
  have hOpen : IsOpen A := hA.2
  simpa using
    (Topology.P1_iff_P3_of_isOpen (A := A) hOpen).symm

theorem Topology.interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior A) := by
  intro x hx
  exact subset_closure hx

theorem Topology.P3_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P3 A := by
  intro hClopen
  exact Topology.P3_of_isOpen (A := A) hClopen.2

theorem Topology.P3_inter_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (closure A) → Topology.P3 (closure B) → Topology.P3 (closure A ∩ closure B) := by
  intro hA hB
  have hA_closed : IsClosed (closure A) := isClosed_closure
  have hB_closed : IsClosed (closure B) := isClosed_closure
  exact
    Topology.P3_inter
      (A := closure A) (B := closure B)
      hA_closed hB_closed
      hA hB

theorem Topology.dense_interior_of_P1_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense A → Dense (interior A) := by
  intro hP1 hDense
  -- From `P1`, we have `A ⊆ closure (interior A)`.
  have hA : (A : Set X) ⊆ closure (interior A) := hP1
  -- Taking closures preserves inclusion.
  have hClosure : closure A ⊆ closure (interior A) := by
    have h := closure_mono hA
    simpa [closure_closure] using h
  -- Because `A` is dense, its closure is `univ`.
  have hUniv : (Set.univ : Set X) ⊆ closure (interior A) := by
    simpa [hDense.closure_eq] using hClosure
  -- Conclude that `closure (interior A) = univ`.
  have hEq : closure (interior A) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; simp
    · exact hUniv
  -- Translate the closure equality into density.
  exact (dense_iff_closure_eq).2 hEq

theorem Topology.P2_iff_P3_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h₁ : Topology.P2 A ↔ Topology.P1 A :=
    (Topology.P2_iff_P1_of_isClopen (A := A) hA)
  have h₂ : Topology.P1 A ↔ Topology.P3 A :=
    (Topology.P3_iff_P1_of_isClopen (A := A) hA).symm
  exact h₁.trans h₂

theorem Topology.P3_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) :
    Topology.P3 A := by
  -- A closed and dense set coincides with `univ`.
  have hEq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (A := A) hClosed hDense
  -- `univ` trivially satisfies `P3`.
  have hP3_univ : Topology.P3 (Set.univ : Set X) :=
    P3_univ (X := X)
  -- Transfer the property via the set equality.
  simpa [hEq] using hP3_univ

theorem Topology.P3_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  -- `closure (interior A)` is always a closed set.
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  -- Apply the general equivalence for closed sets.
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
        (A := closure (interior A)) hClosed)

theorem Topology.P3_diff_of_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) (hA : IsClosed A) :
    Topology.P3 (B \ A) := by
  -- The set `B \ A = B ∩ Aᶜ` is the intersection of two open sets,
  -- hence it is open.
  have hOpen : IsOpen (B \ A) :=
    hB.inter ((isOpen_compl_iff).2 hA)
  -- Every open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := B \ A) hOpen

theorem Topology.P2_and_P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A := by
  constructor
  · rintro ⟨hP2, _⟩
    exact (Topology.P2_iff_isOpen_of_isClosed (A := A) hA).1 hP2
  · intro hOpen
    exact And.intro
      (Topology.P2_of_isOpen (A := A) hOpen)
      (Topology.P3_of_isOpen (A := A) hOpen)

theorem P1_iff_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P1_iff_P3_of_isOpen (A := interior A) hOpen)

theorem Topology.interior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, A i) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- We show that `x` belongs to the interior of each `A i`.
  have h : ∀ i, x ∈ interior (A i) := by
    intro i
    -- Since `⋂ i, A i ⊆ A i`, monotonicity of `interior` yields the claim.
    have hsubset : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ i
    have hInt : interior (⋂ j, A j) ⊆ interior (A i) := interior_mono hsubset
    exact hInt hx
  -- Combine the individual memberships into the intersection.
  exact Set.mem_iInter.2 h

theorem Topology.dense_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Dense A) (hB : Dense B) : Dense (A ∪ B) := by
  -- Compute the closure of the union using `closure_union`.
  have hclosure : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    calc
      closure (A ∪ B : Set X)
          = closure A ∪ closure B := by
            simpa [closure_union]
      _ = (Set.univ : Set X) := by
            simp [hA.closure_eq, hB.closure_eq]
  -- Translate the closure equality back into a density statement.
  exact (dense_iff_closure_eq).2 hclosure

theorem Topology.dense_union_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense A → Dense (A ∪ B) := by
  intro hA
  have hclosure : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    simp [closure_union, hA.closure_eq]
  exact (dense_iff_closure_eq).2 hclosure



theorem Topology.P1_diff_of_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P1 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ) := by
    simpa using (isOpen_compl_iff).2 hB
  -- `A \ B` is the intersection of two open sets, hence open.
  have hOpen : IsOpen (A \ B) := by
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A \ B) hOpen

theorem Topology.P2_union_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (interior A) → Topology.P2 (A ∪ B) := by
  intro hDense
  -- First, obtain density of `interior (A ∪ B)` from the given hypothesis.
  have hDenseUnion : Dense (interior (A ∪ B)) :=
    Topology.dense_interior_union_of_dense_left (A := A) (B := B) hDense
  -- Apply the existing lemma to conclude the `P2` property.
  exact Topology.P2_of_dense_interior (A := A ∪ B) hDenseUnion

theorem Topology.P2_closure_union_iff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (closure (A ∪ B)) ↔ Topology.P2 (closure A ∪ closure B) := by
  have h : closure (A ∪ B : Set X) = closure A ∪ closure B := by
    simpa [closure_union]
  constructor
  · intro hP2
    simpa [h] using hP2
  · intro hP2
    simpa [h] using hP2

theorem Topology.P3_union_of_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : Dense B) :
    Topology.P3 (A ∪ B) := by
  have h : Topology.P3 (B ∪ A) :=
    Topology.P3_union_of_dense_left (A := B) (B := A) hB
  simpa [Set.union_comm] using h

theorem Topology.P1_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) :
    Topology.P1 A := by
  -- A closed and dense set coincides with the whole space.
  have hEq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (A := A) hClosed hDense
  -- `P1` holds for `Set.univ`, hence it also holds for `A`.
  simpa [hEq] using (P1_univ (X := X))

theorem Topology.P1_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (closure A) → Topology.P1 (closure B) → Topology.P1 (closure A ∪ closure B) := by
  intro hA hB
  simpa using (Topology.P1_union (A := closure A) (B := closure B) hA hB)

theorem Topology.P1_P2_P3_of_isClopen_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  intro hA
  simpa using
    (Topology.P1_P2_P3_of_isClopen (A := Aᶜ) hA.compl)

theorem Topology.P1_closure_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = closure (interior A)) :
    Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  intro x hx
  -- Rewrite `x ∈ closure A` using the given equality.
  have hx' : x ∈ closure (interior A) := by
    simpa [h] using hx
  -- Show that this closure is contained in `closure (interior (closure A))`.
  have hsubset : closure (interior A) ⊆ closure (interior (closure A)) := by
    have hinner : interior A ⊆ interior (closure A) := by
      apply interior_mono
      exact (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono hinner
  exact hsubset hx'

theorem Topology.closure_inter_subset_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure B := by
  -- `A ∩ B` is contained in `B`.
  have hsubset : (A ∩ B : Set X) ⊆ B := by
    intro x hx
    exact hx.2
  -- Taking closures preserves this inclusion.
  exact closure_mono hsubset

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  -- First, `interior A ⊆ interior (closure A)` by monotonicity of `interior`.
  have h₁ : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Second, every set is contained in the closure of itself.
  have h₂ : interior (closure A) ⊆ closure (interior (closure A)) := by
    intro x hx
    exact subset_closure hx
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem Topology.closure_interior_eq_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  -- First, upgrade `P2` to `P1` using closedness of `A`.
  have hP1 : Topology.P1 A :=
    Topology.P1_of_P2_of_isClosed (A := A) hA hP2
  -- Apply the existing lemma that establishes the desired equality from `P1`.
  exact Topology.closure_interior_eq_of_isClosed_of_P1 (A := A) hA hP1

theorem Topology.P2_union_of_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : Dense (interior B)) :
    Topology.P2 (A ∪ B) := by
  -- First, obtain density of `interior (A ∪ B)` by symmetry.
  have hDense : Dense (interior (A ∪ B)) := by
    have h := Topology.dense_interior_union_of_dense_left (A := B) (B := A) hB
    simpa [Set.union_comm] using h
  -- Apply the existing lemma to conclude the `P2` property.
  exact Topology.P2_of_dense_interior (A := A ∪ B) hDense



theorem Topology.closure_iInter_closure_eq_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, closure (A i)) = ⋂ i, closure (A i) := by
  apply Set.Subset.antisymm
  ·
    have h :
        closure (⋂ i, closure (A i)) ⊆ ⋂ i, closure (closure (A i)) :=
      Topology.closure_iInter_subset (A := fun i => closure (A i))
    simpa [closure_closure] using h
  ·
    intro x hx
    exact
      (subset_closure :
        (⋂ i, closure (A i)) ⊆ closure (⋂ i, closure (A i))) hx

theorem Topology.closure_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (A i) : Set X) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hsubset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hsubset hxAi

theorem Topology.dense_iUnion_of_nonempty
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Dense (A i)) (hNE : Nonempty ι) :
    Dense (⋃ i, A i) := by
  classical
  -- We will show that `closure (⋃ i, A i) = univ`.
  have h_closure_eq_univ : closure (⋃ i, A i) = (Set.univ : Set X) := by
    -- Prove the two inclusions separately.
    apply Set.Subset.antisymm
    · -- The closure is always contained in `univ`.
      intro x _
      simp
    · -- For the reverse inclusion we use a fixed index coming from `hNE`.
      intro x _
      rcases hNE with ⟨i₀⟩
      -- `x` is in the closure of `A i₀` because that closure is `univ`.
      have hx_closure_i₀ : x ∈ closure (A i₀) := by
        have : closure (A i₀) = (Set.univ : Set X) := (hA i₀).closure_eq
        simpa [this] using (by simp : x ∈ (Set.univ : Set X))
      -- Monotonicity of `closure` upgrades the membership.
      have h_subset : closure (A i₀) ⊆ closure (⋃ i, A i) := by
        have h_incl : (A i₀ : Set X) ⊆ ⋃ i, A i := by
          intro y hy
          exact Set.mem_iUnion.2 ⟨i₀, hy⟩
        exact closure_mono h_incl
      exact h_subset hx_closure_i₀
  -- Translate the closure equality into a density statement.
  exact (dense_iff_closure_eq).2 h_closure_eq_univ

theorem Topology.P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using
    (Topology.P1_P2_P3_of_isOpen (A := (Set.univ : Set X)) hOpen)

theorem Topology.isClosed_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (interior A) ∪ closure (interior B)) := by
  have hA : IsClosed (closure (interior A)) := isClosed_closure
  have hB : IsClosed (closure (interior B)) := isClosed_closure
  exact hA.union hB

theorem Topology.P2_of_isClosed_and_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) :
    Topology.P2 A := by
  have hEq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (A := A) hClosed hDense
  simpa [hEq] using (P2_univ (X := X))

theorem Topology.closure_interior_closure_interior_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) :
    closure (interior (closure (interior A))) = (Set.univ : Set X) := by
  -- Since `interior A` is dense, its closure is the whole space.
  have h1 : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  -- Rewriting with `h1` and using the facts that both `interior` and `closure`
  -- of `univ` yield `univ`, we obtain the desired equality.
  simpa [h1, interior_univ, closure_univ]

theorem Topology.P1_and_P3_iff_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  simpa using (Topology.P2_iff_P1_and_P3 (A := A)).symm

theorem Topology.P1_and_P3_iff_P2' {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  simpa using (Topology.P2_iff_P1_and_P3 (A := A)).symm

theorem Topology.interior_closure_eq_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClopen A) :
    interior (closure A) = (A : Set X) := by
  exact
    Topology.interior_closure_eq_of_isClosed_of_isOpen
      (A := A) hA.1 hA.2

theorem Topology.interior_iUnion_eq_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (A : ι → Set X)
    (hA : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i) = ⋃ i, A i := by
  -- The union of the `A i` is open because each `A i` is open.
  have hOpen : IsOpen (⋃ i, A i) := by
    apply isOpen_iUnion
    intro i
    exact hA i
  -- For an open set `S`, `interior S = S`.
  simpa using hOpen.interior_eq

theorem Topology.closure_interior_closure_interior_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (interior (closure (interior A))) = closure A := by
  intro hP2
  -- From `P2` we have `closure A = closure (interior A)`.
  have h₁ : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  -- The nested `closure ∘ interior` expression contracts to `closure (interior A)`.
  have h₂ :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior (A := A)
  -- Combine the two equalities.
  simpa [h₁] using h₂

theorem Topology.dense_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Dense (closure A) := by
  intro hDense
  exact (Topology.dense_closure_iff_dense (A := A)).mpr hDense

theorem Topology.P2_diff_of_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P2 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen (Bᶜ) := by
    simpa using (isOpen_compl_iff).2 hB
  -- `A \ B` is the intersection of two open sets, hence open.
  have hOpen : IsOpen (A \ B) := by
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A \ B) hOpen

theorem Topology.dense_union_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense B → Dense (A ∪ B) := by
  intro hB
  simpa [Set.union_comm] using
    (Topology.dense_union_left (A := B) (B := A) hB)

theorem Topology.P1_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A = B) :
    Topology.P1 A ↔ Topology.P1 B := by
  cases h
  rfl

theorem Topology.interior_eq_of_isClosed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  have h := Topology.interior_closure_eq_of_isClosed_of_P3 (A := A) hA hP3
  simpa [hA.closure_eq] using h

theorem Topology.P2_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A = B) :
    Topology.P2 A ↔ Topology.P2 B := by
  cases h
  rfl

theorem Topology.closure_interior_union_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
  -- The union of two open sets is open.
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  -- For an open set `S`, `interior S = S`.
  have hInt : interior (A ∪ B) = A ∪ B := hOpen.interior_eq
  -- Rewrite and use the `closure_union` lemma.
  simpa [hInt, closure_union]

theorem Topology.P1_P2_P3_iff_isClopen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsClopen A := by
  -- First, use the existing equivalence between the triple property and openness.
  have hOpenEquiv :
      (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A :=
    Topology.P1_P2_P3_iff_isOpen_of_isClosed (A := A) hA
  -- Establish the desired equivalence with clopeness.
  constructor
  · -- From the triple property, deduce openness and hence clopeness.
    intro hTriple
    have hOpen : IsOpen A := hOpenEquiv.mp hTriple
    exact ⟨hA, hOpen⟩
  · -- From clopeness, obtain openness and hence the triple property.
    intro hClopen
    have hOpen : IsOpen A := hClopen.2
    exact hOpenEquiv.mpr hOpen

theorem Topology.closure_diff_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} : closure (A \ B) ⊆ closure A := by
  intro x hx
  have hsubset : (A \ B : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  exact (closure_mono hsubset) hx

theorem Topology.interior_inter_open_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    intro x hx
    -- `x` belongs to `A ∩ B`
    have hxAB : x ∈ A ∩ B :=
      (interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx
    -- Extract the individual facts
    have hxA : x ∈ A := hxAB.1
    -- Monotonicity of `interior` yields `x ∈ interior B`
    have hxIntB : x ∈ interior B := by
      have hsubset : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact (interior_mono hsubset) hx
    exact And.intro hxA hxIntB
  · -- `⊇` direction
    intro x hx
    -- Separate the hypotheses
    have hxA : x ∈ A := hx.1
    have hxIntB : x ∈ interior B := hx.2
    -- Basic facts about `interior B`
    have hOpenIntB : IsOpen (interior B) := isOpen_interior
    have hIntSubsetB : (interior B : Set X) ⊆ B := interior_subset
    -- Consider the open set `V = interior B ∩ A`
    have hVopen : IsOpen ((interior B) ∩ A) := hOpenIntB.inter hA
    have hxV : x ∈ (interior B) ∩ A :=
      And.intro hxIntB hxA
    -- `V` is contained in `A ∩ B`
    have hVsubset : ((interior B) ∩ A : Set X) ⊆ A ∩ B := by
      intro y hy
      have hyIntB : y ∈ interior B := hy.1
      have hyA    : y ∈ A := hy.2
      have hyB    : y ∈ B := hIntSubsetB hyIntB
      exact And.intro hyA hyB
    -- Hence `x` is in the interior of `A ∩ B`
    have : x ∈ interior (A ∩ B) := by
      -- `interior_maximal` turns the inclusion of the open set `V`
      -- into an inclusion in the interior.
      have hsubsetInt : ((interior B) ∩ A : Set X) ⊆ interior (A ∩ B) := by
        apply interior_maximal hVsubset hVopen
      exact hsubsetInt hxV
    exact this

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  -- Step 1: `x` lies in the closure of `interior A`.
  have hx_closure_int :
      x ∈ closure (interior A) :=
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) hx
  -- Step 2: `closure (interior A)` is contained in `closure A`.
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Combine the two facts to conclude.
  exact hsubset hx_closure_int

theorem Topology.dense_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (closure A) := by
  intro hDenseInt
  -- First, use density of `interior A` to see that `closure A = univ`.
  have hEq : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDenseInt
  -- Taking the closure once more does not change the set.
  have hEq' : closure (closure A) = (Set.univ : Set X) := by
    simpa [closure_closure] using hEq
  -- Translate the equality into a density statement.
  exact (dense_iff_closure_eq).2 hEq'

theorem Topology.P1_of_between_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hBclosure : B ⊆ closure A) (hP1 : Topology.P1 A) :
    Topology.P1 B := by
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxB
  -- Step 1: promote `x ∈ B` to `x ∈ closure A`.
  have hx_closureA : x ∈ closure A := hBclosure hxB
  -- Step 2: use `P1` for `A` to move into `closure (interior A)`.
  have hClA_sub_ClIntA : closure A ⊆ closure (interior A) := by
    -- Since `A ⊆ closure (interior A)`, taking closures yields the claim.
    have hA_sub : (A : Set X) ⊆ closure (interior A) := hP1
    have h := closure_mono hA_sub
    simpa [closure_closure] using h
  have hx_closureIntA : x ∈ closure (interior A) :=
    hClA_sub_ClIntA hx_closureA
  -- Step 3: enlarge to `closure (interior B)` using monotonicity.
  have hIntA_sub_IntB : interior A ⊆ interior B :=
    interior_mono hAB
  have hClIntA_sub_ClIntB : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hIntA_sub_IntB
  exact hClIntA_sub_ClIntB hx_closureIntA

theorem Topology.closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure (interior B) := by
  intro x hx
  -- `A ∩ interior B` is contained in `A`.
  have hA : (A ∩ interior B : Set X) ⊆ A := by
    intro y hy; exact hy.1
  -- `A ∩ interior B` is also contained in `interior B`.
  have hB : (A ∩ interior B : Set X) ⊆ interior B := by
    intro y hy; exact hy.2
  -- Taking closures preserves inclusions.
  have hxA : x ∈ closure A := (closure_mono hA) hx
  have hxB : x ∈ closure (interior B) := (closure_mono hB) hx
  exact And.intro hxA hxB

theorem interior_closure_comp {X : Type*} [TopologicalSpace X] :
    ((fun A : Set X => interior (closure A)) ∘
        (fun A : Set X => interior (closure A))) =
      (fun A : Set X => interior (closure A)) := by
  funext A
  simp [Function.comp,
    Topology.interior_closure_interior_closure_eq_interior_closure]

theorem closure_interior_comp
    {X : Type*} [TopologicalSpace X] :
    ((fun A : Set X => closure (interior A)) ∘
        (fun A : Set X => closure (interior A))) =
      (fun A : Set X => closure (interior A)) := by
  funext A
  simp [Function.comp,
    Topology.closure_interior_closure_interior_eq_closure_interior (A := A)]

theorem Topology.dense_interior_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (interior (closure A)) := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have hClIntA : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- `interior A` is contained in `interior (closure A)`.
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Taking closures preserves inclusion.
  have hClSubset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono hsubset
  -- Therefore `closure (interior (closure A))` contains `univ`.
  have hUnivSubset :
      (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
    simpa [hClIntA] using hClSubset
  -- The reverse inclusion is trivial.
  have hSubsetUniv :
      closure (interior (closure A)) ⊆ (Set.univ : Set X) := by
    intro x _; simp
  -- Conclude that the closure equals `univ`.
  have hEq :
      closure (interior (closure A)) = (Set.univ : Set X) :=
    Set.Subset.antisymm hSubsetUniv hUnivSubset
  -- Translate the closure equality into a density statement.
  exact (dense_iff_closure_eq).2 hEq

theorem interior_closure_interior_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (interior (∅ : Set X))) = (∅ : Set X) := by
  simp

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  -- First we show  `interior (A ∩ B) ⊆ interior A ∩ B`.
  have h₁ : interior (A ∩ B) ⊆ interior A ∩ B := by
    intro x hx
    -- `x` belongs to the interior of `A`, because `A ∩ B ⊆ A`.
    have hxA : x ∈ interior A := by
      have hsub : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact (interior_mono hsub) hx
    -- `x` belongs to the interior of `B`, because `A ∩ B ⊆ B`.
    have hxB_int : x ∈ interior B := by
      have hsub : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact (interior_mono hsub) hx
    -- Since `B` is open, `interior B = B`.
    have hxB : x ∈ B := by
      simpa [hB.interior_eq] using hxB_int
    exact And.intro hxA hxB
  -- Now we prove the reverse inclusion `interior A ∩ B ⊆ interior (A ∩ B)`.
  have h₂ : interior A ∩ B ⊆ interior (A ∩ B) := by
    intro x hx
    have hxA : x ∈ interior A := hx.1
    have hxB : x ∈ B := hx.2
    -- The set `interior A ∩ B` is open since it is the intersection of two open sets.
    have hOpen : IsOpen (interior A ∩ B) :=
      isOpen_interior.inter hB
    -- Moreover, it is contained in `A ∩ B`.
    have hsubset : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    -- Therefore every point of `interior A ∩ B` lies in `interior (A ∩ B)`.
    have hIntSubset :
        (interior A ∩ B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal hsubset hOpen
    exact hIntSubset (And.intro hxA hxB)
  -- Combine the two inclusions.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.isClosed_closure_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (interior A) ∩ closure (interior B)) := by
  have hA : IsClosed (closure (interior A)) := isClosed_closure
  have hB : IsClosed (closure (interior B)) := isClosed_closure
  exact hA.inter hB

theorem Topology.interior_diff_subset_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  -- The set difference `A \ B` is contained in `A`.
  have hsubset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Apply monotonicity of `interior` to obtain the desired inclusion.
  exact interior_mono hsubset

theorem Topology.P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Dense A) (hAB : (A : Set X) ⊆ B) : Topology.P3 B := by
  dsimp [Topology.P3]
  intro x hxB
  -- Show that `closure B = univ`.
  have hsub : (Set.univ : Set X) ⊆ closure B := by
    intro y _
    -- Since `closure A = univ`, every point lies in `closure A`.
    have hyA : y ∈ closure A := by
      simpa [hA.closure_eq] using (by simp : y ∈ (Set.univ : Set X))
    -- Monotonicity of `closure` upgrades the membership.
    have hcl : closure A ⊆ closure B := closure_mono hAB
    exact hcl hyA
  have hclosureB : closure B = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; simp
    · exact hsub
  -- Conclude the goal using the computed equality.
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hclosureB, interior_univ] using this

theorem Topology.interior_inter_eq_empty_of_interiors_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : interior A ∩ interior B = (∅ : Set X)) :
    interior (A ∩ B) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ interior A ∩ interior B :=
      (Topology.interior_inter_subset (A := A) (B := B)) hx
    have : x ∈ (∅ : Set X) := by
      simpa [h] using hx'
    exact this
  · exact Set.empty_subset _

theorem Topology.closure_interior_eq_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) :
    closure (interior A) = (A : Set X) := by
  -- Since `A` is open, its interior is itself.
  have hInt : interior A = (A : Set X) := hA.2.interior_eq
  -- Since `A` is closed, its closure is itself.
  have hCl : closure A = (A : Set X) := hA.1.closure_eq
  -- Rewrite and conclude.
  simpa [hInt, hCl]

theorem Topology.interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interior_closure_interior_closure_eq_interior_closure
      (A := interior A))

theorem Topology.isClosed_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure A ∩ closure B) := by
  have hA : IsClosed (closure A) := isClosed_closure
  have hB : IsClosed (closure B) := isClosed_closure
  exact hA.inter hB

theorem Topology.dense_interior_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro h
    simpa using h.closure_eq
  · intro h
    exact (dense_iff_closure_eq).2 h

theorem Topology.interior_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ⊆ interior (closure (A ∪ B)) := by
  -- First inclusion: `interior A ⊆ interior (closure A)`.
  have h₁ : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  -- Second inclusion: `interior (closure A) ⊆ interior (closure (A ∪ B))`.
  have h₂ : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
    apply interior_mono
    have : closure A ⊆ closure (A ∪ B) := by
      apply closure_mono
      exact Set.subset_union_left
    exact this
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem Topology.interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure A)) :
    interior (closure A) = closure A := by
  simpa using h.interior_eq

theorem Topology.closure_inter_interior_subset_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B : Set X) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior A ∩ interior B` is contained in each individual interior.
  have hA : (interior A ∩ interior B : Set X) ⊆ interior A := by
    intro y hy; exact hy.1
  have hB : (interior A ∩ interior B : Set X) ⊆ interior B := by
    intro y hy; exact hy.2
  -- Apply monotonicity of `closure` to obtain the desired memberships.
  have hxA : x ∈ closure (interior A) := (closure_mono hA) hx
  have hxB : x ∈ closure (interior B) := (closure_mono hB) hx
  exact And.intro hxA hxB

theorem Topology.P3_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  exact Topology.P3_of_P3_closure (A := A) hP3

theorem Topology.dense_interior_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Dense (interior (closure A)) := by
  intro hDense
  -- Since `A` is dense, its closure is the whole space.
  have hClA : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the interior of that closure is also the whole space.
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hClA, interior_univ]
  -- Taking closures preserves this equality.
  have hClInt : closure (interior (closure A)) = (Set.univ : Set X) := by
    simpa [hInt, closure_univ]
  -- Conclude density from the closure equality.
  exact (dense_iff_closure_eq).2 hClInt

theorem Topology.P3_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure A)) : Topology.P3 (closure A) := by
  exact (Topology.P3_closure_iff_isOpen_closure (A := A)).2 h



theorem Topology.closure_interior_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∪ B)) ⊆ closure A ∪ closure B := by
  intro x hx
  -- Step 1: `interior (A ∪ B)` is contained in `A ∪ B`.
  have h₁ : interior (A ∪ B) ⊆ (A ∪ B : Set X) := interior_subset
  -- Step 2: Taking closures preserves the inclusion.
  have h₂ : closure (interior (A ∪ B)) ⊆ closure (A ∪ B) :=
    closure_mono h₁
  -- Step 3: Rewrite `closure (A ∪ B)` using `closure_union`.
  have hx' : x ∈ closure (A ∪ B) := h₂ hx
  simpa [closure_union] using hx'

theorem Topology.isClosed_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure A ∪ closure B) := by
  have hA : IsClosed (closure A) := isClosed_closure
  have hB : IsClosed (closure B) := isClosed_closure
  exact hA.union hB

theorem Topology.P3_interior_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (interior (A ∩ B)) := by
  have hOpen : IsOpen (interior (A ∩ B)) := isOpen_interior
  exact Topology.P3_of_isOpen (A := interior (A ∩ B)) hOpen

theorem Topology.P3_closure_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 (closure A) := by
  intro hP2
  have hClosed : IsClosed (closure A) := isClosed_closure
  have hOpen : IsOpen (closure A) :=
    Topology.isOpen_of_P2_of_isClosed (A := closure A) hClosed hP2
  exact Topology.P3_of_isOpen (A := closure A) hOpen

theorem Topology.interior_inter_eq_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ interior B := by
  calc
    interior (A ∩ B) = A ∩ B := (hA.inter hB).interior_eq
    _ = interior A ∩ interior B := by
      simpa [hA.interior_eq, hB.interior_eq]

theorem Topology.P2_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior A ∩ interior B) := by
  -- `interior A` and `interior B` are open, so their intersection is open.
  have hOpen : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := interior A ∩ interior B) hOpen

theorem Topology.closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior (closure A) = interior (closure A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact And.intro (interior_subset hx) hx

theorem Topology.P1_union_interior_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (A ∪ interior A) := by
  intro hP1A
  have hP1Int : Topology.P1 (interior A) := P1_interior (A := A)
  exact Topology.P1_union (A := A) (B := interior A) hP1A hP1Int

theorem Topology.P3_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A = B) :
    Topology.P3 A ↔ Topology.P3 B := by
  cases h
  rfl

theorem Topology.P1_interior_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∩ interior B) := by
  -- Both `interior A` and `interior B` are open.
  have hOpenA : IsOpen (interior A) := isOpen_interior
  have hOpenB : IsOpen (interior B) := isOpen_interior
  -- The intersection of two open sets is open, hence satisfies `P1`.
  exact Topology.P1_inter_of_isOpen
    (A := interior A) (B := interior B) hOpenA hOpenB



theorem Topology.isClosed_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure A \ interior A) := by
  -- `closure A` is closed.
  have hClosedCl : IsClosed (closure A) := isClosed_closure
  -- The complement of an open set is closed.
  have hClosedCompl : IsClosed ((interior A)ᶜ) :=
    (isOpen_interior : IsOpen (interior A)).isClosed_compl
  -- Rewrite the set difference as an intersection and use `IsClosed.inter`.
  simpa [Set.diff_eq] using hClosedCl.inter hClosedCompl

theorem Topology.dense_closure_interior_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (closure (interior A)) := by
  intro hDense
  have hEq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  simpa [hEq] using dense_univ

theorem Topology.closure_interior_iUnion_eq_closure_iUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (A : ι → Set X)
    (hA : ∀ i, IsOpen (A i)) :
    closure (interior (⋃ i, A i)) = closure (⋃ i, A i) := by
  -- The union of the `A i` is open because each `A i` is open.
  have hOpen : IsOpen (⋃ i, A i) := by
    apply isOpen_iUnion
    intro i
    exact hA i
  -- For an open set `S`, its interior is itself.
  have hInt : interior (⋃ i, A i) = (⋃ i, A i) := hOpen.interior_eq
  -- Rewriting with `hInt` gives the desired equality.
  simpa [hInt]

theorem Topology.P3_of_P1_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P2 A → Topology.P3 A := by
  intro hP1 hP2
  -- From `P2` we obtain both `P1` and `P3`; extract the latter.
  exact ((Topology.P2_iff_P1_and_P3 (A := A)).1 hP2).2

theorem Topology.union_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ((A : Set X) ∪ interior A) = A := by
  simpa using
    (Set.union_eq_left.2
      (interior_subset : (interior A : Set X) ⊆ A))

theorem Topology.P1_union_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P1 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  exact Topology.P1_of_isOpen (A := A ∪ B) hOpen

theorem Topology.isClopen_iff_closed_and_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A ↔ IsClosed A ∧ interior A = (A : Set X) := by
  constructor
  · intro h
    have hClosed : IsClosed A := h.1
    have hOpen : IsOpen A := h.2
    have hInt : interior A = (A : Set X) := hOpen.interior_eq
    exact And.intro hClosed hInt
  · rintro ⟨hClosed, hInt⟩
    have hOpen : IsOpen A := by
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hInt] using hOpenInt
    exact And.intro hClosed hOpen

theorem Topology.dense_interior_closure_interior_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (interior (closure (interior A))) := by
  intro hDense
  -- We already have that `closure (interior (closure (interior A))) = univ`.
  have hEq :
      closure (interior (closure (interior A))) = (Set.univ : Set X) :=
    Topology.closure_interior_closure_interior_eq_univ_of_dense_interior
      (A := A) hDense
  -- Translate the closure equality into a density statement.
  exact (dense_iff_closure_eq).2 hEq

theorem Topology.P2_union_interior_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P2 (A ∪ interior A) := by
  intro hP2A
  have hP2Int : Topology.P2 (interior A) := P2_interior (A := A)
  simpa using
    (Topology.P2_union (A := A) (B := interior A) hP2A hP2Int)

theorem Topology.interior_closure_interior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (interior (⋂ i, A i))) ⊆
      ⋂ i, interior (closure (interior (A i))) := by
  intro x hx
  -- Show that `x` belongs to each component of the intersection.
  have h : ∀ i, x ∈ interior (closure (interior (A i))) := by
    intro i
    -- Step 1: `(⋂ j, A j) ⊆ A i`
    have h₁ : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ i
    -- Step 2: `interior (⋂ j, A j) ⊆ interior (A i)`
    have h₂ : interior (⋂ j, A j) ⊆ interior (A i) := interior_mono h₁
    -- Step 3: `closure (interior (⋂ j, A j)) ⊆ closure (interior (A i))`
    have h₃ : closure (interior (⋂ j, A j)) ⊆ closure (interior (A i)) :=
      closure_mono h₂
    -- Step 4: `interior (closure (interior (⋂ j, A j))) ⊆
    --          interior (closure (interior (A i)))`
    have h₄ :
        interior (closure (interior (⋂ j, A j))) ⊆
          interior (closure (interior (A i))) :=
      interior_mono h₃
    -- Apply the inclusion to `hx`.
    exact h₄ hx
  exact Set.mem_iInter.2 h

theorem closure_interior_closure_comp
    {X : Type*} [TopologicalSpace X] :
    ((fun A : Set X => closure (interior (closure A))) ∘
        (fun A : Set X => closure (interior (closure A)))) =
      (fun A : Set X => closure (interior (closure A))) := by
  funext A
  -- Abbreviate `F S = closure (interior (closure S))`.
  have h₁ :
      closure (interior (closure (closure (interior (closure A))))) =
        closure (interior (closure (interior (closure A)))) := by
    -- First contraction: remove the outermost redundant `closure`.
    simpa using
      (Topology.closure_interior_closure_closure_eq_closure_interior_closure
        (A := interior (closure A)))
  have h₂ :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    -- Second contraction: collapse the nested `interior`.
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (A := closure A))
  -- Combine the two equalities to obtain idempotence.
  simpa [Function.comp] using (h₁.trans h₂)

theorem Topology.closure_inter_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed (A ∩ B) := hA.inter hB
  -- A closed set is equal to its closure.
  simpa [hClosed.closure_eq]

theorem Topology.interior_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior A ⊆ closure B := by
  intro x hxInt
  -- From `x ∈ interior A`, we obtain `x ∈ A`.
  have hxA : x ∈ A := interior_subset hxInt
  -- Use the given inclusion `A ⊆ B` to get `x ∈ B`.
  have hxB : x ∈ B := hAB hxA
  -- Every point of `B` lies in `closure B`.
  exact subset_closure hxB

theorem Topology.interior_subset_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ⊆ interior (A ∪ B) := by
  exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)

theorem Topology.P1_iff_closure_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)` we get the desired inclusion by taking closures.
    have h : (A : Set X) ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using this
  · intro hSub
    -- Use the assumed inclusion and the fact that `x ∈ A` implies `x ∈ closure A`.
    dsimp [Topology.P1] at *
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    exact hSub hx_closure

theorem Topology.eq_empty_of_P1_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = (∅ : Set X)) (hP1 : Topology.P1 A) :
    (A : Set X) = (∅ : Set X) := by
  have hsubset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    have hx_cl : x ∈ closure (interior A) := hP1 hx
    simpa [hInt, closure_empty] using hx_cl
  exact Set.Subset.antisymm hsubset (Set.empty_subset _)

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = s := by
  ext x
  simp

theorem Topology.interior_closure_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B : Set X)) ⊆ closure A ∪ closure B := by
  intro x hx
  -- From `hx : x ∈ interior (closure (A ∪ B))` we first deduce that
  -- `x` lies in `closure (A ∪ B)` by `interior_subset`.
  have hcl : x ∈ closure (A ∪ B : Set X) := interior_subset hx
  -- Next, rewrite `closure (A ∪ B)` using `closure_union`.
  -- This shows `x ∈ closure A ∪ closure B`, as desired.
  simpa [closure_union] using hcl

theorem Topology.P1_union_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (interior A) → Topology.P1 (A ∪ B) := by
  intro hDense
  -- `A` itself satisfies `P1`.
  have hP1A : Topology.P1 A :=
    Topology.P1_of_dense_interior (A := A) hDense
  -- Since `interior A` is dense, its closure is the whole space.
  have hClosure : closure (interior A) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Hence every element of `B` lies in `closure (interior A)`.
  have hSubset : (B : Set X) ⊆ closure (interior A) := by
    intro x hxB
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hClosure] using this
  -- Apply the existing lemma to conclude the result.
  exact
    Topology.P1_union_of_subset (A := A) (B := B) hP1A hSubset

theorem Topology.P3_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (interior (A ∪ B)) := by
  have hOpen : IsOpen (interior (A ∪ B)) := isOpen_interior
  exact Topology.P3_of_isOpen (A := interior (A ∪ B)) hOpen

theorem Topology.closure_inter_interior_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hxA : x ∈ A := interior_subset hx
    have hxCl : x ∈ closure A := subset_closure hxA
    exact And.intro hxCl hx

theorem Topology.isOpen_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsOpen (closure A) := by
  intro hDense
  have hEq : closure A = (Set.univ : Set X) := hDense.closure_eq
  simpa [hEq] using isOpen_univ