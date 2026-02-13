

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  exact fun x hxA => interior_subset (hP2 hxA)

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono hcl
  exact hsubset hx₁

theorem Topology.isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Topology.P1 A := by
  intro hA
  intro x hxA
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  exact subset_closure hx_int

theorem Topology.dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 A := by
  intro hDense
  intro x _
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hDense.closure_eq, interior_univ] using this

theorem Topology.isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Topology.P3 A := by
  intro hA
  intro x hxA
  have hsubset : (A : Set X) ⊆ interior (closure A) := by
    have hcl : (A : Set X) ⊆ closure A := subset_closure
    exact interior_maximal hcl hA
  exact hsubset hxA

theorem Topology.isOpen_dense_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Dense A → Topology.P2 A := by
  intro hOpen hDense
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hOpen.interior_eq, hDense.closure_eq, interior_univ] using this

theorem Topology.isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Topology.P2 A := by
  intro hOpen
  intro x hxA
  have hsubset : (A : Set X) ⊆ interior (closure A) := by
    have hcl : (A : Set X) ⊆ closure A := subset_closure
    exact interior_maximal hcl hOpen
  have hx' : x ∈ interior (closure A) := hsubset hxA
  simpa [hOpen.interior_eq] using hx'

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  simpa using (Topology.isOpen_implies_P1 (A := interior A) isOpen_interior)

theorem Topology.P1_implies_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → closure A ⊆ closure (interior A) := by
  intro hP1
  have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
  simpa [closure_closure] using h

theorem Topology.P1_implies_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → closure (interior A) = closure A := by
  intro hP1
  have h₁ : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have h₂ : closure A ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  exact subset_antisymm h₁ h₂

theorem Topology.P2_implies_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → closure (interior A) = closure A := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.P1_implies_closure_interior_eq_closure (A := A) hP1

theorem Topology.P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  · intro hEq
    -- we must show A ⊆ closure (interior A)
    intro x hxA
    have hx_closureA : x ∈ closure A := subset_closure hxA
    simpa [hEq] using hx_closureA

theorem Topology.isOpen_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P2 A ↔ Topology.P3 A) := by
  intro hOpen
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (A := A) hP2
  · intro hP3
    intro x hxA
    have hx : x ∈ interior (closure A) := hP3 hxA
    simpa [hOpen.interior_eq] using hx

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_implies_P3 (A := interior A) hOpen

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem Topology.P2_implies_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (interior A)) = interior (closure A) := by
  intro hP2
  have h := Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  simpa using congrArg interior h

theorem Topology.P1_implies_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (closure (interior A)) = interior (closure A) := by
  intro hP1
  have h := Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  simpa using congrArg interior h

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    have hcl : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_maximal hcl isOpen_interior
  have hx' : x ∈ interior (closure (interior A)) := hsubset hx
  simpa [interior_interior] using hx'

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem Topology.P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact
      ⟨Topology.P2_implies_P1 (A := A) hP2,
        Topology.P2_implies_P3 (A := A) hP2⟩
  · rintro ⟨hP1, hP3⟩
    intro x hxA
    have hx₁ : x ∈ interior (closure A) := hP3 hxA
    have hsubset : interior (closure A) ⊆ interior (closure (interior A)) := by
      have hcl : closure A ⊆ closure (interior A) :=
        Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
      exact interior_mono hcl
    exact hsubset hx₁

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem Topology.P3_implies_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A ⊆ closure (interior (closure A)) := by
  intro hP3
  exact closure_mono hP3

theorem Topology.isOpen_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen A → closure (interior A) = closure A := by
  intro hA
  have hP2 : Topology.P2 A := Topology.isOpen_implies_P2 (A := A) hA
  exact Topology.P2_implies_closure_interior_eq_closure (A := A) hP2

theorem Topology.P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense A → Topology.P2 A := by
  intro hP1 hDense
  have hP3 : Topology.P3 A := Topology.dense_implies_P3 (A := A) hDense
  exact (Topology.P2_iff_P1_and_P3 (A := A)).mpr ⟨hP1, hP3⟩

theorem Topology.P3_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure (interior (closure A)) = closure A := by
  intro hP3
  apply subset_antisymm
  ·
    have h : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    have h' : closure (interior (closure A)) ⊆ closure A := by
      have h₁ := closure_mono h
      simpa [closure_closure] using h₁
    exact h'
  ·
    exact
      Topology.P3_implies_closure_subset_closure_interior_closure
        (A := A) hP3

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hP1A hP1B
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hP1A hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have h₁ : interior A ⊆ interior (A ∪ B) := by
          have hAUB : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hAUB
        exact closure_mono h₁
      exact hsubset hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hP1B hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h₁ : interior B ⊆ interior (A ∪ B) := by
          have hAUB : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hAUB
        exact closure_mono h₁
      exact hsubset hx_closure

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP3B
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      -- `x` belongs to `A`
      have hx_int : x ∈ interior (closure A) := hP3A hxA
      -- `closure A` is contained in `closure (A ∪ B)`
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure A ⊆ closure (A ∪ B) := by
          have hAUB : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact closure_mono hAUB
        exact interior_mono hcl
      exact hsubset hx_int
  | inr hxB =>
      -- `x` belongs to `B`
      have hx_int : x ∈ interior (closure B) := hP3B hxB
      -- `closure B` is contained in `closure (A ∪ B)`
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure B ⊆ closure (A ∪ B) := by
          have hBUB : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact closure_mono hBUB
        exact interior_mono hcl
      exact hsubset hx_int

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hP2A hP2B
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      -- `x` belongs to `A`
      have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
      -- relate the targets
      have hsubset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        -- first on closures
        have hcl : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          -- first on interiors
          have hsub : interior A ⊆ interior (A ∪ B) := by
            have hAB : (A : Set X) ⊆ A ∪ B := by
              intro y hy
              exact Or.inl hy
            exact interior_mono hAB
          exact closure_mono hsub
        exact interior_mono hcl
      exact hsubset hx_int
  | inr hxB =>
      -- `x` belongs to `B`
      have hx_int : x ∈ interior (closure (interior B)) := hP2B hxB
      -- relate the targets
      have hsubset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        -- first on closures
        have hcl : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          -- first on interiors
          have hsub : interior B ⊆ interior (A ∪ B) := by
            have hBB : (B : Set X) ⊆ A ∪ B := by
              intro y hy
              exact Or.inr hy
            exact interior_mono hBB
          exact closure_mono hsub
        exact interior_mono hcl
      exact hsubset hx_int

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem Topology.P1_nonempty_implies_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior A).Nonempty := by
  intro hP1 hA_nonempty
  rcases hA_nonempty with ⟨x, hxA⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  by_cases hIntEq : interior A = ∅
  ·
    have hFalse : False := by
      simpa [hIntEq, closure_empty] using hx_cl
    exact hFalse.elim
  ·
    classical
    exact Set.nonempty_iff_ne_empty.mpr hIntEq

theorem Topology.isClosed_P3_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → Topology.P1 A := by
  intro hClosed hP3
  intro x hxA
  -- From `P3`, `x` is in the interior of `closure A`, but since `A` is closed,
  -- `closure A = A`, so `x` is in `interior A`.
  have hx_int : x ∈ interior A := by
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hClosed.closure_eq] using this
  -- Any point of `interior A` is certainly in `closure (interior A)`.
  exact subset_closure hx_int

theorem Topology.P2_implies_closure_interior_closure_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior (closure A)) = closure A := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact Topology.P3_implies_closure_interior_closure_eq_closure (A := A) hP3

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  intro x hx_closureA
  -- First, from `P1 A`, we know `closure A ⊆ closure (interior A)`.
  have hx₁ : x ∈ closure (interior A) := by
    have hsubset : closure A ⊆ closure (interior A) :=
      Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
    exact hsubset hx_closureA
  -- Next, `interior A ⊆ interior (closure A)`; taking closures preserves inclusion.
  have hsubset₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    have hInt : (interior A : Set X) ⊆ interior (closure A) := by
      -- `A ⊆ closure A`, hence the same holds for interiors.
      have hIncl : (A : Set X) ⊆ closure A := subset_closure
      exact interior_mono hIncl
    exact closure_mono hInt
  -- Combining the two inclusions yields the desired membership.
  exact hsubset₂ hx₁

theorem Topology.P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  intro x hx_closureA
  have hsubset : (closure A : Set X) ⊆ closure (interior (closure A)) :=
    Topology.P3_implies_closure_subset_closure_interior_closure (A := A) hP3
  exact hsubset hx_closureA

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  exact (Topology.P1_closure_of_P1 (A := interior A)) (Topology.P1_interior (A := A))

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P1 (s i)) → Topology.P1 (⋃ i, s i) := by
  intro hP1
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hx_i⟩
  have hx_closure : x ∈ closure (interior (s i)) := (hP1 i) hx_i
  have hsubset : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    have hInt : interior (s i) ⊆ interior (⋃ j, s j) := by
      have hSub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hSub
    exact closure_mono hInt
  exact hsubset hx_closure

theorem Topology.P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.P1_closure_of_P1 (A := A) hP1

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P3 (s i)) → Topology.P3 (⋃ i, s i) := by
  intro hP3
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hx_i⟩
  have hx_int : x ∈ interior (closure (s i)) := (hP3 i) hx_i
  have hsubset : interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) := by
    have hcl : closure (s i) ⊆ closure (⋃ j, s j) := by
      have hSub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono hSub
    exact interior_mono hcl
  exact hsubset hx_int

theorem Topology.P2_iff_closure_interior_eq_closure_and_P3 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (closure (interior A) = closure A ∧ Topology.P3 A) := by
  -- We will shuttle between the existing equivalences
  -- `P2 A ↔ P1 A ∧ P3 A` and `P1 A ↔ closure (interior A) = closure A`.
  have h₁ := (Topology.P2_iff_P1_and_P3 (A := A))
  have h₂ := (Topology.P1_iff_closure_interior_eq_closure (A := A))
  constructor
  · intro hP2
    -- From `P2`, obtain `P1` and `P3`.
    rcases (h₁).1 hP2 with ⟨hP1, hP3⟩
    -- Turn `P1` into the closure equality.
    have hEq : closure (interior A) = closure A := (h₂).1 hP1
    exact ⟨hEq, hP3⟩
  · rintro ⟨hEq, hP3⟩
    -- The closure equality gives `P1`.
    have hP1 : Topology.P1 A := (h₂).2 hEq
    -- Combine `P1` and `P3` to recover `P2`.
    exact (h₁).2 ⟨hP1, hP3⟩

theorem Topology.P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  constructor
  · intro hP3
    -- From `P3 (closure A)` we get `closure A ⊆ interior (closure (closure A))`,
    -- which, after simplifying, becomes `closure A ⊆ interior (closure A)`.
    have hsubset : (closure (A : Set X)) ⊆ interior (closure (closure (A : Set X))) := hP3
    have hsubset' : (closure (A : Set X)) ⊆ interior (closure (A : Set X)) := by
      simpa [closure_closure] using hsubset
    -- Together with the always-true inclusion `interior (closure A) ⊆ closure A`,
    -- we obtain equality.
    have hEq : interior (closure (A : Set X)) = closure (A : Set X) := by
      apply subset_antisymm
      · exact interior_subset
      · exact hsubset'
    -- An equality with an open set (`interior (closure A)`) yields openness.
    have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using this
  · intro hOpen
    -- If `closure A` is open, then its interior is itself, giving `P3`.
    intro x hx
    have hIntEq : interior (closure (A : Set X)) = closure (A : Set X) := by
      simpa using hOpen.interior_eq
    have : x ∈ interior (closure (A : Set X)) := by
      simpa [hIntEq] using hx
    simpa [closure_closure] using this

theorem Topology.P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P3 (A := interior (closure A)) hOpen

theorem Topology.P2_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → (Topology.P2 A ↔ Topology.P1 A) := by
  intro hDense
  have hP3 : Topology.P3 A := Topology.dense_implies_P3 (A := A) hDense
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    exact (Topology.P2_implies_P1 (A := A) hP2)
  · intro hP1
    have : Topology.P1 A ∧ Topology.P3 A := And.intro hP1 hP3
    exact (hEquiv).2 this

theorem Topology.isClosed_P1_implies_closure_interior_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P1 A → closure (interior A) = A := by
  intro hClosed hP1
  have hEq : closure (interior A) = closure A :=
    Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  simpa [hClosed.closure_eq] using hEq

theorem Topology.P3_nonempty_implies_interior_closure_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP3 hA_nonempty
  rcases hA_nonempty with ⟨x, hxA⟩
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  exact ⟨x, hx_int⟩

theorem Topology.P1_implies_closure_interior_closure_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (interior (closure A)) = closure A := by
  intro hP1
  -- `closure A` itself satisfies `P1`
  have hP1_closure : Topology.P1 (closure A) :=
    Topology.P1_closure_of_P1 (A := A) hP1
  -- Apply the known equality for `P1 (closure A)`
  have hEq :=
    Topology.P1_implies_closure_interior_eq_closure (A := closure A) hP1_closure
  simpa [closure_closure] using hEq

theorem isOpen_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A ↔ interior A = A := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using this

theorem Topology.isClosed_isOpen_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (IsOpen A ↔ Topology.P3 A) := by
  intro hClosed
  constructor
  · intro hOpen
    exact Topology.isOpen_implies_P3 (A := A) hOpen
  · intro hP3
    have hSub : (A : Set X) ⊆ interior A := by
      have : (A : Set X) ⊆ interior (closure A) := hP3
      simpa [hClosed.closure_eq] using this
    have hEq : interior A = A := by
      apply subset_antisymm interior_subset hSub
    exact (isOpen_iff_interior_eq (A := A)).2 hEq

theorem Topology.P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  simpa using
    (Topology.isOpen_implies_P2 (A := interior (closure A)) isOpen_interior)

theorem Topology.isClosed_P3_implies_interior_closure_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → interior (closure A) = A := by
  intro hClosed hP3
  apply subset_antisymm
  ·
    intro x hx
    have : x ∈ closure A := interior_subset hx
    simpa [hClosed.closure_eq] using this
  ·
    intro x hxA
    exact hP3 hxA

theorem Topology.P2_iff_P3_of_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure (interior A) = closure A) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- Obtain `P1 A` from the given closure equality.
  have hP1 : Topology.P1 A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).2 hEq
  -- Use the existing equivalence `P2 A ↔ P1 A ∧ P3 A`.
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (A := A) hP2
  · intro hP3
    have : Topology.P1 A ∧ Topology.P3 A := And.intro hP1 hP3
    exact (hEquiv).2 this

theorem Topology.P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3Closure
  intro x hxA
  have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have hx_int : x ∈ interior (closure (closure (A : Set X))) := hP3Closure hx_closure
  simpa [closure_closure] using hx_int

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P2 (s i)) → Topology.P2 (⋃ i, s i) := by
  intro hP2
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hx_i⟩
  have hx_int : x ∈ interior (closure (interior (s i))) := (hP2 i) hx_i
  have hsubset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    -- First, relate the interiors.
    have hInt : interior (s i) ⊆ interior (⋃ j, s j) := by
      have hSub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hSub
    -- Take closures of both sides.
    have hCl : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) :=
      closure_mono hInt
    -- Finally, take interiors again.
    exact interior_mono hCl
  exact hsubset hx_int

theorem Topology.P2_nonempty_implies_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior A).Nonempty := by
  intro hP2 hA_nonempty
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact
    Topology.P1_nonempty_implies_interior_nonempty (A := A) hP1 hA_nonempty

theorem Topology.dense_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  intro hDense
  simpa [hDense.closure_eq, interior_univ, closure_univ]

theorem Topology.isClosed_P3_iff_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → (Topology.P3 A ↔ interior A = A) := by
  intro hClosed
  have h₁ := (Topology.isClosed_isOpen_iff_P3 (A := A) hClosed)
  have h₂ := (isOpen_iff_interior_eq (A := A))
  simpa using (h₁.symm.trans h₂)

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) := by
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  exact Topology.isOpen_implies_P1 (A := interior (closure A)) hOpen

theorem Topology.isClosed_P2_implies_closure_interior_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P2 A → closure (interior A) = A := by
  intro hClosed hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact
    Topology.isClosed_P1_implies_closure_interior_eq_self (A := A) hClosed hP1

theorem Topology.P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (Topology.P2 A ↔ Topology.P3 A) := by
  intro hP1
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    have h := (hEquiv).1 hP2
    exact h.right
  · intro hP3
    exact (hEquiv).2 ⟨hP1, hP3⟩

theorem Topology.isClosed_P3_implies_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → IsOpen A := by
  intro hClosed hP3
  have hIntEq : interior A = A := by
    have h := Topology.isClosed_P3_implies_interior_closure_eq_self (A := A) hClosed hP3
    simpa [hClosed.closure_eq] using h
  have : IsOpen (interior A) := isOpen_interior
  simpa [hIntEq] using this

theorem Topology.dense_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P1 (closure (A : Set X)) := by
  intro hDense
  have hP3 : Topology.P3 (A : Set X) := Topology.dense_implies_P3 (A := A) hDense
  exact Topology.P1_closure_of_P3 (A := A) hP3

theorem Topology.isClosed_P1_iff_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → (Topology.P1 A ↔ closure (interior A) = A) := by
  intro hClosed
  constructor
  · intro hP1
    exact
      Topology.isClosed_P1_implies_closure_interior_eq_self (A := A) hClosed hP1
  · intro hEq
    -- Since `A` is closed, `closure A = A`.
    have hClosure : closure (A : Set X) = A := hClosed.closure_eq
    -- Rewrite the given equality to match the characterisation of `P1`.
    have hEq' : closure (interior A) = closure A := by
      simpa [hClosure] using hEq
    -- Apply the equivalence `P1 A ↔ closure (interior A) = closure A`.
    exact
      (Topology.P1_iff_closure_interior_eq_closure (A := A)).mpr hEq'

theorem Topology.isOpen_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P3 A := by
  intro hOpen
  have hP3Closure : Topology.P3 (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen_closure (A := A)).2 hOpen
  exact (Topology.P3_closure_implies_P3 (A := A)) hP3Closure

theorem Topology.isClosed_P2_implies_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P2 A → IsOpen A := by
  intro hClosed hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact Topology.isClosed_P3_implies_isOpen (A := A) hClosed hP3

theorem Topology.isClosed_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → Topology.P2 A := by
  intro hClosed hP3
  have hP1 : Topology.P1 A :=
    Topology.isClosed_P3_implies_P1 (A := A) hClosed hP3
  exact (Topology.P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩

theorem Topology.dense_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P2 (closure (A : Set X)) := by
  intro hDense
  intro x hx
  -- Since `A` is dense, `closure A = univ`, so `x` is trivially in `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [hDense.closure_eq] using hx
  -- Unravel the goal using the fact that every set equals `univ`.
  simpa [hDense.closure_eq, interior_univ, closure_univ] using hx_univ

theorem Topology.isOpen_closure_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hOpen
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  have hP3 : Topology.P3 (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen_closure (A := A)).2 hOpen
  exact
    (Topology.isClosed_P3_implies_P2 (A := closure (A : Set X))) hClosed hP3

theorem Topology.isClosed_P2_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (Topology.P2 A ↔ IsOpen A) := by
  intro hClosed
  constructor
  · intro hP2
    exact Topology.isClosed_P2_implies_isOpen (A := A) hClosed hP2
  · intro hOpen
    have hP3 : Topology.P3 A := Topology.isOpen_implies_P3 (A := A) hOpen
    exact Topology.isClosed_P3_implies_P2 (A := A) hClosed hP3

theorem Topology.isClosed_P2_implies_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → Topology.P2 A → interior A = A := by
  intro hClosed hP2
  have hOpen : IsOpen A := Topology.isClosed_P2_implies_isOpen (A := A) hClosed hP2
  simpa using hOpen.interior_eq

theorem Topology.isClosed_isOpen_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (IsOpen A ↔ (Topology.P1 A ∧ Topology.P3 A)) := by
  intro hClosed
  have h₁ : IsOpen A ↔ Topology.P2 A :=
    (Topology.isClosed_P2_iff_isOpen (A := A) hClosed).symm
  have h₂ : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) :=
    (Topology.P2_iff_P1_and_P3 (A := A))
  simpa using h₁.trans h₂

theorem Topology.isClosed_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (Topology.P2 A ↔ Topology.P3 A) := by
  intro hClosed
  have h₁ := (Topology.isClosed_P2_iff_isOpen (A := A) hClosed)
  have h₂ := (Topology.isClosed_isOpen_iff_P3 (A := A) hClosed)
  simpa using h₁.trans h₂

theorem Topology.P2_iff_P3_of_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure (interior A)) = interior (closure A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    intro x hxA
    have : x ∈ interior (closure (interior A)) := hP2 hxA
    simpa [hEq] using this
  · intro hP3
    intro x hxA
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hEq] using this

theorem Topology.P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.isClosed_P2_iff_isOpen (A := closure (A : Set X)) hClosed)

theorem Topology.dense_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (closure (A : Set X)) := by
  intro hDense
  intro x _
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hDense.closure_eq, interior_univ, closure_closure] using this

theorem Topology.isOpen_implies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  intro hOpen
  exact
    ⟨Topology.isOpen_implies_P1 (A := A) hOpen,
      Topology.isOpen_implies_P2 (A := A) hOpen,
      Topology.isOpen_implies_P3 (A := A) hOpen⟩

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (A : Set X)))) := by
  simpa using
    (Topology.P1_closure_interior (A := closure (A : Set X)))

theorem Topology.P3_closure_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  exact
    Topology.isClosed_P3_implies_P2 (A := closure (A : Set X)) hClosed hP3

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A : Set X, A ∈ 𝒜 → Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hP1
  intro x hx_sUnion
  rcases Set.mem_sUnion.1 hx_sUnion with ⟨A, hA_mem, hxA⟩
  have hx_closure : x ∈ closure (interior A) := (hP1 A hA_mem) hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    have hInt : (interior A : Set X) ⊆ interior (⋃₀ 𝒜) := by
      have hSub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact interior_mono hSub
    exact closure_mono hInt
  exact hsubset hx_closure

theorem Topology.P2_iff_P1_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    Topology.P2 A ↔ Topology.P1 A := by
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    exact ((hEquiv).1 hP2).left
  · intro hP1
    exact (hEquiv).2 ⟨hP1, hP3⟩

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A : Set X, A ∈ 𝒜 → Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hP3
  intro x hx_sUnion
  rcases Set.mem_sUnion.1 hx_sUnion with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure (A : Set X)) := (hP3 A hA_mem) hxA
  have hsubset : interior (closure (A : Set X)) ⊆ interior (closure (⋃₀ 𝒜 : Set X)) := by
    have hcl : closure (A : Set X) ⊆ closure (⋃₀ 𝒜 : Set X) := by
      have hSub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact closure_mono hSub
    exact interior_mono hcl
  exact hsubset hx_int

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A : Set X, A ∈ 𝒜 → Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro hP2
  intro x hx_sUnion
  rcases Set.mem_sUnion.1 hx_sUnion with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := (hP2 A hA_mem) hxA
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜 : Set X))) := by
    -- First, relate the interiors of `A` and `⋃₀ 𝒜`.
    have hInt : interior A ⊆ interior (⋃₀ 𝒜 : Set X) := by
      have hSub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact interior_mono hSub
    -- Take closures of both sides.
    have hCl : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜 : Set X)) :=
      closure_mono hInt
    -- Finally, take interiors again.
    exact interior_mono hCl
  exact hsubset hx_int

theorem Topology.P3_iff_exists_open_superset_subset_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3
    refine
      ⟨interior (closure (A : Set X)), isOpen_interior,
        ?_, interior_subset⟩
    intro x hxA
    exact hP3 hxA
  · rintro ⟨U, hOpenU, hA_sub_U, hU_sub_cl⟩
    intro x hxA
    have hxU : x ∈ U := hA_sub_U hxA
    have hU_sub_int : U ⊆ interior (closure (A : Set X)) :=
      interior_maximal hU_sub_cl hOpenU
    exact hU_sub_int hxU

theorem Topology.isOpen_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P1 A ↔ Topology.P2 A) := by
  intro hOpen
  constructor
  · intro _hP1
    exact Topology.isOpen_implies_P2 (A := A) hOpen
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  -- Step 1: `x` lies in the closure of `interior A`.
  have hx₁ : x ∈ closure (interior A) := interior_subset hx
  -- Step 2: `closure (interior A)` is contained in `closure A`.
  have hx₂ : (closure (interior A) : Set X) ⊆ closure A :=
    closure_mono interior_subset
  -- Combining the two inclusions yields the result.
  exact hx₂ hx₁

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure (A : Set X)) := by
  have h₁ := (Topology.P2_closure_iff_isOpen_closure (A := A))
  have h₂ := (Topology.P3_closure_iff_isOpen_closure (A := A)).symm
  exact h₁.trans h₂

theorem Topology.isOpen_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P1 A ↔ Topology.P3 A) := by
  intro hOpen
  have h₁ := (Topology.isOpen_P1_iff_P2 (A := A) hOpen)
  have h₂ := (Topology.isOpen_P2_iff_P3 (A := A) hOpen)
  simpa using h₁.trans h₂

theorem Topology.P1_interior_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.isOpen_P1_iff_P2 (A := interior A) hOpen)

theorem Topology.P2_iff_exists_open_superset_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure (interior A) := by
  constructor
  · intro hP2
    refine
      ⟨interior (closure (interior A)), isOpen_interior, ?_, interior_subset⟩
    intro x hxA
    exact hP2 hxA
  · rintro ⟨U, hOpenU, hA_sub_U, hU_sub_cl⟩
    intro x hxA
    have hxU : x ∈ U := hA_sub_U hxA
    have hU_sub_int : U ⊆ interior (closure (interior A)) :=
      interior_maximal hU_sub_cl hOpenU
    exact hU_sub_int hxU

theorem Topology.P2_of_P1_and_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → IsOpen (closure (A : Set X)) → Topology.P2 A := by
  intro hP1 hOpenCl
  have hP3 : Topology.P3 A := Topology.isOpen_closure_implies_P3 (A := A) hOpenCl
  exact (Topology.P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩

theorem Topology.P1_union_implies_closure_interior_eq_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B →
      closure (interior (A ∪ B)) = closure (A ∪ B) := by
  intro hP1A hP1B
  -- First, `A ∪ B` satisfies `P1` by the corresponding union lemma.
  have hP1Union : Topology.P1 (A ∪ B) :=
    Topology.P1_union (A := A) (B := B) hP1A hP1B
  -- Apply the characterization of `P1` in terms of closures.
  exact
    Topology.P1_implies_closure_interior_eq_closure
      (A := A ∪ B) hP1Union

theorem Topology.interior_closure_interior_subset_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
  exact interior_mono hcl

theorem Topology.isOpen_subset_closure_implies_subset_interior_closure {X : Type*}
    [TopologicalSpace X] {A U : Set X} :
    IsOpen U → closure U ⊆ closure (A : Set X) →
      U ⊆ interior (closure (A : Set X)) := by
  intro hOpen hClosureSub
  -- First, note that every point of `U` lies in `closure U`, hence in `closure A`.
  have hU_sub_closureA : (U : Set X) ⊆ closure (A : Set X) := by
    intro x hxU
    have : x ∈ closure U := subset_closure hxU
    exact hClosureSub this
  -- Apply the maximality of `interior` with the open set `U`.
  exact interior_maximal hU_sub_closureA hOpen

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  ·
    have h₁ :
        (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    have h₁ :
        (interior A : Set X) ⊆ interior (closure (interior A)) := by
      have hSub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      exact interior_maximal hSub isOpen_interior
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂

theorem Topology.isOpen_closure_P2_iff_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → (Topology.P2 A ↔ Topology.P1 A) := by
  intro hOpenCl
  -- From the openness of `closure A`, we obtain `P3 A`.
  have hP3 : Topology.P3 A :=
    Topology.isOpen_closure_implies_P3 (A := A) hOpenCl
  -- Use the existing equivalence `P2 A ↔ P1 A ∧ P3 A`.
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    -- Extract `P1 A` from `P2 A`.
    exact ((hEquiv).1 hP2).1
  · intro hP1
    -- Combine `P1 A` with the known `P3 A` to obtain `P2 A`.
    exact (hEquiv).2 ⟨hP1, hP3⟩

theorem Topology.P1_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U := by
  constructor
  · intro hP1
    refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
    intro x hxA
    exact hP1 hxA
  · rintro ⟨U, hOpenU, hU_sub_A, hA_sub_clU⟩
    intro x hxA
    have hx_clU : x ∈ closure U := hA_sub_clU hxA
    have hU_sub_intA : (U : Set X) ⊆ interior A :=
      interior_maximal hU_sub_A hOpenU
    have h_clU_sub : (closure U : Set X) ⊆ closure (interior A) :=
      closure_mono hU_sub_intA
    exact h_clU_sub hx_clU

theorem Topology.closure_interior_closure_subset_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure A := by
  -- `interior (closure A)` is contained in `closure A`
  have h : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
    interior_subset
  -- Taking closures preserves inclusions; simplify with `closure_closure`
  simpa [closure_closure] using closure_mono h

theorem Topology.P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2Cl
  have hP3Cl : Topology.P3 (closure (A : Set X)) :=
    (Topology.P2_closure_iff_P3_closure (A := A)).1 hP2Cl
  exact (Topology.P3_closure_implies_P3 (A := A)) hP3Cl

theorem Topology.interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior A ⊆ interior (closure (interior A)) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  have hSub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  exact interior_maximal hSub hOpen

theorem Topology.dense_implies_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A → interior (closure (A : Set X)) = (Set.univ : Set X) := by
  intro hDense
  simpa [hDense.closure_eq, interior_univ]

theorem Topology.isOpen_iUnion_implies_P2 {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} :
    (∀ i, IsOpen (s i)) → Topology.P2 (⋃ i, s i) := by
  intro hOpen
  have hOpenUnion : IsOpen (⋃ i, s i) := isOpen_iUnion (fun i => hOpen i)
  exact Topology.isOpen_implies_P2 (A := ⋃ i, s i) hOpenUnion

theorem Topology.interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  apply subset_antisymm
  ·
    have hsubset :
        closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
      Topology.closure_interior_closure_subset_closure (A := A)
    exact interior_mono hsubset
  ·
    have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    have hsubset :
        (interior (closure (A : Set X)) : Set X) ⊆
          closure (interior (closure (A : Set X))) := by
      intro x hx
      exact subset_closure hx
    have hsubset' :
        (interior (closure (A : Set X)) : Set X) ⊆
          interior (closure (interior (closure (A : Set X)))) :=
      interior_maximal hsubset hOpen
    exact hsubset'

theorem Topology.isClosed_isOpen_iff_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A →
      (IsOpen A ↔ (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A)) := by
  intro hClosed
  have h₁ := (Topology.isClosed_isOpen_iff_P1_and_P3 (A := A) hClosed)
  have h₂ := (Topology.isClosed_P2_iff_isOpen (A := A) hClosed)
  constructor
  · intro hOpen
    have hP1P3 : Topology.P1 A ∧ Topology.P3 A := (h₁).1 hOpen
    have hP2 : Topology.P2 A := (h₂).2 hOpen
    exact ⟨hP1P3.1, hP2, hP1P3.2⟩
  · rintro ⟨_, hP2, _⟩
    exact (h₂).1 hP2

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  have hcl : (closure (A : Set X)) ⊆ closure (B : Set X) := closure_mono hAB
  exact interior_mono hcl

theorem Topology.P1_iff_P3_of_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure (A : Set X)) = closure (interior A)) :
    Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro hP1
    intro x hxA
    have hx : x ∈ closure (interior A) := hP1 hxA
    simpa [hEq.symm] using hx
  · intro hP3
    intro x hxA
    have hx : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hEq] using hx

theorem Topology.P2_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    (Topology.isOpen_implies_P2 (A := interior (closure (interior A))) hOpen)

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (A : Set X)) := by
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem Topology.P3_interior_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using
    (Topology.isOpen_P2_iff_P3 (A := interior A) hOpen).symm

theorem Topology.dense_implies_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsOpen (closure (A : Set X)) := by
  intro hDense
  simpa [hDense.closure_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))

theorem Topology.closure_interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆ closure (interior (closure A)) := by
  have h :
      (interior (closure (interior A)) : Set X) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure (A := A)
  exact closure_mono h

theorem Topology.P1_interior_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  simpa using
    ((Topology.P1_interior_iff_P2_interior (A := A)).trans
      ((Topology.P3_interior_iff_P2_interior (A := A)).symm))

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- First, enlarge the innermost interiors using the inclusion `A ⊆ B`.
  have hInt : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusions.
  have hCl : (closure (interior A) : Set X) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Finally, taking interiors preserves inclusions once more.
  exact interior_mono hCl

theorem Topology.P2_implies_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → (A : Set X) ⊆ interior (closure (A : Set X)) := by
  intro hP2
  exact Topology.P2_implies_P3 (A := A) hP2

theorem Topology.isClosed_isOpen_iff_P1_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (IsOpen A ↔ (Topology.P1 A ∧ Topology.P2 A)) := by
  intro hClosed
  have h₁ : IsOpen A ↔ Topology.P2 A :=
    (Topology.isClosed_P2_iff_isOpen (A := A) hClosed).symm
  constructor
  · intro hOpen
    have hP2 : Topology.P2 A := (h₁).1 hOpen
    have hP1 : Topology.P1 A := Topology.isOpen_implies_P1 (A := A) hOpen
    exact And.intro hP1 hP2
  · rintro ⟨_, hP2⟩
    exact (Topology.isClosed_P2_implies_isOpen (A := A)) hClosed hP2

theorem Topology.P3_implies_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → (A : Set X) ⊆ interior (closure (A : Set X)) := by
  intro hP3 x hxA
  exact hP3 hxA

theorem Topology.P1_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P1 (A := interior (closure (interior A))) hOpen

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  have hInt : (interior A : Set X) ⊆ interior B := interior_mono hAB
  exact closure_mono hInt

theorem Topology.P3_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P3 (A := interior (closure (interior A))) hOpen

theorem Topology.P2_nonempty_implies_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP2 hA_nonempty
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact
    Topology.P3_nonempty_implies_interior_closure_nonempty
      (A := A) hP3 hA_nonempty

theorem Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  have h :=
    Topology.interior_closure_interior_closure_eq_interior_closure (A := A)
  simpa using congrArg closure h

theorem Topology.P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  exact (Topology.P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩

theorem Topology.interior_closure_inter_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ B) : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- Step 1: relate `closure (A ∩ B)` to `closure A` and `closure B`
  have hclA : closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
    have hsub : ((A ∩ B) : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact closure_mono hsub
  have hclB : closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
    have hsub : ((A ∩ B) : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact closure_mono hsub
  -- Step 2: use monotonicity of `interior` to obtain the desired memberships
  have hxA : x ∈ interior (closure (A : Set X)) :=
    (interior_mono hclA) hx
  have hxB : x ∈ interior (closure (B : Set X)) :=
    (interior_mono hclB) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (A : Set X))) = interior (closure (A : Set X)) := by
  simpa [closure_closure]

theorem Topology.interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP1 x hx_int_cl
  -- First inclusion: `interior (closure A) ⊆ closure A`.
  have hx_clA : x ∈ closure (A : Set X) := interior_subset hx_int_cl
  -- Second inclusion provided by `P1 A`: `closure A ⊆ closure (interior A)`.
  have h_cl_subset :
      (closure (A : Set X)) ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  exact h_cl_subset hx_clA

theorem Topology.P1_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hEq : closure (interior A) = (A : Set X)) :
    Topology.P1 A := by
  intro x hxA
  simpa [hEq] using hxA

theorem Topology.isClosed_P2_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (Topology.P2 A ↔ interior A = A) := by
  intro hClosed
  constructor
  · intro hP2
    exact Topology.isClosed_P2_implies_interior_eq_self (A := A) hClosed hP2
  · intro hIntEq
    -- From `interior A = A`, we obtain that `A` is open.
    have hOpen : IsOpen A := (isOpen_iff_interior_eq (A := A)).2 hIntEq
    -- Any open set satisfies `P2`.
    exact Topology.isOpen_implies_P2 (A := A) hOpen

theorem Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
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

theorem Topology.interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ⊆
      interior (closure ((A ∪ B) : Set X)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` lies in `interior (closure A)`
      -- We expand this to `interior (closure (A ∪ B))` using monotonicity.
      have hsub : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have hcl : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono hsub
      have hint : interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hcl
      exact hint hxA
  | inr hxB =>
      -- Symmetric argument for `B`.
      have hsub : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hcl : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono hsub
      have hint : interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hcl
      exact hint hxB

theorem Topology.P2_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P2 A := by
  intro hEq
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hEq, interior_univ] using this

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- Step 1: move from `interior (closure (interior A))` to `interior (closure A)`.
  have hx₁ : x ∈ interior (closure A) :=
    (Topology.interior_closure_interior_subset_interior_closure (A := A)) hx
  -- Step 2: every point of `interior (closure A)` lies in `closure (interior (closure A))`.
  exact (subset_closure hx₁)

theorem Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interior_closure_interior_closure_eq_interior_closure
      (A := interior A))

theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` lies in `interior A`, hence also in `interior (A ∪ B)`
      have hAB : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have hsubset : (interior A : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono hAB
      exact hsubset hxA
  | inr hxB =>
      -- `x` lies in `interior B`, hence also in `interior (A ∪ B)`
      have hBB : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hsubset : (interior B : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono hBB
      exact hsubset hxB

theorem Topology.closure_interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ closure (interior A)`; transport along the inclusions
      have hsubset :
          closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) := by
        -- first relate the interiors
        have hInt : (interior (A : Set X)) ⊆ interior (A ∪ B) := by
          have hSub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hSub
        -- taking closures preserves inclusion
        exact closure_mono hInt
      exact hsubset hxA
  | inr hxB =>
      -- symmetric argument for the second summand
      have hsubset :
          closure (interior (B : Set X)) ⊆ closure (interior (A ∪ B)) := by
        have hInt : (interior (B : Set X)) ⊆ interior (A ∪ B) := by
          have hSub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hSub
        exact closure_mono hInt
      exact hsubset hxB

theorem Topology.closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  simpa using (closure_mono (interior_subset : (interior A : Set X) ⊆ A))

theorem Topology.isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Topology.P1 (closure (A : Set X)) := by
  intro hOpen
  have hP1A : Topology.P1 (A : Set X) :=
    Topology.isOpen_implies_P1 (A := A) hOpen
  exact Topology.P1_closure_of_P1 (A := A) hP1A

theorem interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ interior B ⊆ interior (A ∩ B : Set X) := by
  intro x hx
  -- `interior A` and `interior B` are open.
  have hOpen : IsOpen (interior A ∩ interior B) :=
    (isOpen_interior).inter isOpen_interior
  -- Their intersection is contained in `A ∩ B`.
  have hSub : (interior A ∩ interior B : Set X) ⊆ (A ∩ B) := by
    intro y hy
    exact And.intro (interior_subset hy.1) (interior_subset hy.2)
  -- By maximality of the interior, the intersection is contained in
  -- `interior (A ∩ B)`.
  have hIncl : (interior A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
    interior_maximal hSub hOpen
  exact hIncl hx

theorem Topology.P3_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed A → IsClosed B → Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hClosedA hClosedB hP3A hP3B
  -- From closedness and `P3`, we infer that both `A` and `B` are open.
  have hOpenA : IsOpen A :=
    Topology.isClosed_P3_implies_isOpen (A := A) hClosedA hP3A
  have hOpenB : IsOpen B :=
    Topology.isClosed_P3_implies_isOpen (A := B) hClosedB hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (A := A ∩ B) hOpenInter

theorem Topology.P3_implies_eq_empty_of_empty_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → interior (closure (A : Set X)) = ∅ → A = (∅ : Set X) := by
  intro hP3 hIntEq
  ext x
  constructor
  · intro hxA
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hIntEq] using this
  · intro hxEmpty
    cases hxEmpty

theorem Topology.closure_interior_inter_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A ∩ B) : Set X)) ⊆
      closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) := by
  intro x hx
  -- Membership in the left component
  have hxA : x ∈ closure (interior (A : Set X)) := by
    -- `interior (A ∩ B)` is contained in `interior A`
    have hIntSub : (interior ((A ∩ B) : Set X) : Set X) ⊆ interior (A : Set X) := by
      have : ((A ∩ B) : Set X) ⊆ A := by
        intro y hy
        exact hy.1
      exact interior_mono this
    -- Taking closures preserves inclusions
    exact (closure_mono hIntSub) hx
  -- Membership in the right component
  have hxB : x ∈ closure (interior (B : Set X)) := by
    -- `interior (A ∩ B)` is contained in `interior B`
    have hIntSub : (interior ((A ∩ B) : Set X) : Set X) ⊆ interior (B : Set X) := by
      have : ((A ∩ B) : Set X) ⊆ B := by
        intro y hy
        exact hy.2
      exact interior_mono this
    -- Taking closures preserves inclusions
    exact (closure_mono hIntSub) hx
  exact And.intro hxA hxB

theorem Topology.P2_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (A : Set X) → IsClosed (B : Set X) →
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hClosedA hClosedB hP2A hP2B
  -- From closedness and `P2`, we infer that both `A` and `B` are open.
  have hOpenA : IsOpen (A : Set X) :=
    Topology.isClosed_P2_implies_isOpen (A := A) hClosedA hP2A
  have hOpenB : IsOpen (B : Set X) :=
    Topology.isClosed_P2_implies_isOpen (A := B) hClosedB hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen ((A ∩ B) : Set X) := hOpenA.inter hOpenB
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (A := A ∩ B) hOpenInter

theorem Topology.isClosed_isOpen_implies_closure_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → IsOpen A → closure (interior A) = A := by
  intro hClosed hOpen
  simpa [hOpen.interior_eq, hClosed.closure_eq]

theorem Topology.dense_interior_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 A := by
  intro hDenseInt
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hDenseInt.closure_eq, interior_univ] using this

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  -- Step 1: enlarge the inner `closure` using monotonicity.
  have hCl : (closure (A : Set X)) ⊆ closure (B : Set X) := closure_mono hAB
  -- Step 2: apply monotonicity of `interior`.
  have hInt :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (B : Set X)) :=
    interior_mono hCl
  -- Step 3: take closures again to obtain the desired inclusion.
  exact closure_mono hInt

theorem Topology.dense_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ interior (closure (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact
      (Topology.dense_implies_interior_closure_eq_univ (A := A)) hDense
  · intro hIntEq
    -- First, show `closure A = univ`.
    have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      intro x hx
      have hxInt : x ∈ interior (closure (A : Set X)) := by
        simpa [hIntEq] using hx
      exact interior_subset hxInt
    have hClosureEq : closure (A : Set X) = (Set.univ : Set X) := by
      apply subset_antisymm
      · intro x hx; simp
      · exact hSub
    -- Conclude density from the closure equality.
    simpa [Dense, hClosureEq] using hClosureEq

theorem Topology.dense_interior_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P1 A := by
  intro hDenseInt
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hDenseInt.closure_eq] using this

theorem Topology.P1_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P1 A := by
  intro hEq
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hEq] using this

theorem Topology.interior_inter_isOpen_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B : Set X) = A ∩ interior B := by
  apply subset_antisymm
  · -- `⊆` direction: from left to right
    intro x hx
    -- A point in `interior (A ∩ B)` lies in `A ∩ B`
    have hxAB : x ∈ (A ∩ B : Set X) := interior_subset hx
    -- Hence it lies in `A`
    have hxA : x ∈ A := hxAB.1
    -- And, since `A ∩ B ⊆ B`, it also lies in `interior B`
    have hSub : (A ∩ B : Set X) ⊆ (B : Set X) := by
      intro y hy; exact hy.2
    have hxIntB : x ∈ interior (B : Set X) := (interior_mono hSub) hx
    exact And.intro hxA hxIntB
  · -- `⊇` direction: from right to left
    intro x hx
    rcases hx with ⟨hxA, hxIntB⟩
    -- `A ∩ interior B` is an open neighbourhood of `x`
    have hOpen : IsOpen (A ∩ interior (B : Set X) : Set X) :=
      hA.inter isOpen_interior
    -- and is contained in `A ∩ B`
    have hSub : (A ∩ interior (B : Set X) : Set X) ⊆ (A ∩ B : Set X) := by
      intro y hy
      have hyB : y ∈ B := interior_subset hy.2
      exact And.intro hy.1 hyB
    -- Therefore, by maximality of the interior, it is contained in `interior (A ∩ B)`
    have hIncl : (A ∩ interior (B : Set X) : Set X) ⊆
        interior (A ∩ B : Set X) := interior_maximal hSub hOpen
    -- Since `x` lies in `A ∩ interior B`, it also lies in the interior of `A ∩ B`
    have : x ∈ (A ∩ interior (B : Set X) : Set X) := And.intro hxA hxIntB
    exact hIncl this

theorem Topology.interior_closure_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.interior_closure_subset_closure_interior_of_P1 (A := A) hP1

theorem Topology.isOpen_inter_implies_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen A → IsOpen B → Topology.P1 (A ∩ B) := by
  intro hOpenA hOpenB
  have hOpenInter : IsOpen ((A ∩ B) : Set X) := hOpenA.inter hOpenB
  exact Topology.isOpen_implies_P1 (A := A ∩ B) hOpenInter

theorem Topology.P3_iff_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ (A ⊆ interior (closure (A : Set X))) := by
  rfl

theorem Topology.P3_union_of_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P3 A → (B ⊆ interior (closure (A : Set X))) → Topology.P3 (A ∪ B) := by
  intro hP3A hBsub
  intro x hxUnion
  -- First, note that `interior (closure A)` is contained in
  -- `interior (closure (A ∪ B))`; this inclusion will be reused.
  have hsubset : interior (closure (A : Set X)) ⊆
      interior (closure (A ∪ B : Set X)) := by
    -- Since `A ⊆ A ∪ B`, the same holds after taking closures,
    -- and then interiors.
    have hcl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
      have hIncl : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      exact closure_mono hIncl
    exact interior_mono hcl
  -- Now distinguish whether `x` comes from `A` or from `B`.
  cases hxUnion with
  | inl hxA =>
      -- Case `x ∈ A`
      have hx_int : x ∈ interior (closure (A : Set X)) := hP3A hxA
      exact hsubset hx_int
  | inr hxB =>
      -- Case `x ∈ B`
      have hx_int : x ∈ interior (closure (A : Set X)) := hBsub hxB
      exact hsubset hx_int

theorem Topology.interior_closure_eq_closure_of_isOpen_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      interior (closure (A : Set X)) = closure (A : Set X) := by
  intro hOpen
  simpa using hOpen.interior_eq

theorem Topology.P1_implies_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior (closure A)) := by
  intro hP1 x hxA
  -- From `P1 A`, the point `x` lies in `closure (interior A)`.
  have hx_closure_int : (x : X) ∈ closure (interior A) := hP1 hxA
  -- `interior A` is contained in `interior (closure A)` because `A ⊆ closure A`.
  have hInt_sub :
      (interior A : Set X) ⊆ interior (closure A) := by
    have hSub : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono hSub
  -- Taking closures preserves inclusions.
  have hCl_sub :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono hInt_sub
  -- Combining the two, obtain the desired membership.
  exact hCl_sub hx_closure_int

theorem Topology.isOpen_closure_implies_P1_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hOpenCl
  simpa using
    (Topology.isOpen_implies_P1 (A := closure (A : Set X)) hOpenCl)

theorem Topology.interior_inter_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) = interior A ∩ interior B := by
  apply subset_antisymm
  ·
    intro x hx
    -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
    have hA : (interior (A ∩ B : Set X) : Set X) ⊆ interior A := by
      have hSub : ((A ∩ B) : Set X) ⊆ (A : Set X) := by
        intro y hy
        exact hy.1
      exact interior_mono hSub
    have hB : (interior (A ∩ B : Set X) : Set X) ⊆ interior B := by
      have hSub : ((A ∩ B) : Set X) ⊆ (B : Set X) := by
        intro y hy
        exact hy.2
      exact interior_mono hSub
    exact And.intro (hA hx) (hB hx)
  ·
    intro x hx
    -- The reverse inclusion is given by an existing lemma.
    have hsubset :
        (interior A ∩ interior B : Set X) ⊆ interior (A ∩ B : Set X) :=
      interior_inter_subset (A := A) (B := B)
    exact hsubset hx

theorem Topology.interior_closure_interior_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure (interior (closure A))) := by
  -- Step 1: `interior A` is contained in `interior (closure A)`.
  have hInt : (interior A : Set X) ⊆ interior (closure A) := by
    have hSub : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono hSub
  -- Step 2: taking closures preserves inclusions.
  have hCl : (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono hInt
  -- Step 3: taking interiors preserves inclusions once more.
  exact interior_mono hCl

theorem Topology.isOpen_inter_implies_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen A → IsOpen B → Topology.P2 (A ∩ B) := by
  intro hOpenA hOpenB
  have hOpenInter : IsOpen ((A ∩ B) : Set X) := hOpenA.inter hOpenB
  exact Topology.isOpen_implies_P2 (A := A ∩ B) hOpenInter

theorem Topology.isOpen_inter_implies_P3 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen A → IsOpen B → Topology.P3 (A ∩ B) := by
  intro hOpenA hOpenB
  have hOpenInter : IsOpen ((A ∩ B) : Set X) := hOpenA.inter hOpenB
  exact Topology.isOpen_implies_P3 (A := A ∩ B) hOpenInter

theorem Topology.P2_union_of_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → (B ⊆ interior (closure (interior A))) →
      Topology.P2 (A ∪ B) := by
  intro hP2A hBsub
  intro x hxUnion
  -- First, we build a useful inclusion that will be used in both cases.
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (A ∪ B))) := by
    -- Step 1: `interior A ⊆ interior (A ∪ B)`
    have hInt : (interior A : Set X) ⊆ interior (A ∪ B) := by
      have hSub : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      exact interior_mono hSub
    -- Step 2: take closures of both sides
    have hCl : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono hInt
    -- Step 3: take interiors again
    exact interior_mono hCl
  -- Now distinguish whether `x` comes from `A` or from `B`.
  cases hxUnion with
  | inl hxA =>
      -- Case `x ∈ A`
      have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
      exact hsubset hx_int
  | inr hxB =>
      -- Case `x ∈ B`
      have hx_int : x ∈ interior (closure (interior A)) := hBsub hxB
      exact hsubset hx_int

theorem Topology.P2_implies_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A : Set X) ⊆ interior (closure (interior (closure (A : Set X)))) := by
  intro hP2
  intro x hxA
  -- From `P2`, we obtain that `x` lies in `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  -- Use the monotonicity lemma to move further inside the nested closures.
  have hsubset :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (closure (A : Set X)))) :=
    Topology.interior_closure_interior_subset_interior_closure_interior_closure (A := A)
  exact hsubset hx₁

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
      interior (closure (A : Set X)) := by
  -- First, collapse the innermost six-layer expression to a four-layer one.
  have h₁ :
      interior (closure (interior (closure (interior (closure (A : Set X)))))) =
        interior (closure (interior (closure (A : Set X)))) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
        (A := interior (closure (A : Set X))))
  -- Next, collapse the resulting four-layer expression to the desired two-layer one.
  have h₂ :
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure (A : Set X)) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
        (A := A))
  -- Combine the two equalities.
  calc
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
        interior (closure (interior (closure (A : Set X)))) := h₁
    _ = interior (closure (A : Set X)) := h₂

theorem Topology.isOpen_iUnion_implies_P3 {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} :
    (∀ i, IsOpen (s i)) → Topology.P3 (⋃ i, s i) := by
  intro hOpen
  have hOpenUnion : IsOpen (⋃ i, s i) := isOpen_iUnion (fun i => hOpen i)
  exact Topology.isOpen_implies_P3 (A := ⋃ i, s i) hOpenUnion

theorem Topology.interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hxIntA
  -- Step 1: `x` lies in `interior (closure A)` because `A ⊆ closure A`.
  have hxIntClA : x ∈ interior (closure (A : Set X)) := by
    have hSub : (A : Set X) ⊆ closure (A : Set X) := subset_closure
    have hMono : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono hSub
    exact hMono hxIntA
  -- Step 2: every point of `interior (closure A)` lies in its closure.
  exact subset_closure hxIntClA

theorem Topology.P3_closure_interior_iff_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  simpa using
    (Topology.P3_closure_iff_isOpen_closure (A := interior A))

theorem Topology.isOpen_iUnion_implies_P1 {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} :
    (∀ i, IsOpen (s i)) → Topology.P1 (⋃ i, s i) := by
  intro hOpen
  have hOpenUnion : IsOpen (⋃ i, s i) := isOpen_iUnion (fun i => hOpen i)
  exact Topology.isOpen_implies_P1 (A := ⋃ i, s i) hOpenUnion

theorem Topology.nonempty_of_interior_closure_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior (closure (A : Set X))).Nonempty → A.Nonempty := by
  classical
  intro hInt
  -- First, record that the closure of `A` is nonempty.
  have hCl : (closure (A : Set X)).Nonempty := by
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩
  -- We prove the goal by contradiction.
  by_contra hA
  -- From the assumption `¬ A.Nonempty`, deduce that `A = ∅`.
  have hAeq : (A : Set X) = ∅ := by
    simpa [Set.not_nonempty_iff_eq_empty] using hA
  -- Hence the closure of `A` is also empty.
  have hClEq : closure (A : Set X) = (∅ : Set X) := by
    simpa [hAeq] using closure_empty
  -- But `hCl` provides a point in the (empty) closure, a contradiction.
  rcases hCl with ⟨x, hxCl⟩
  have : (x : X) ∈ (∅ : Set X) := by
    simpa [hClEq] using hxCl
  cases this

theorem Topology.P2_implies_eq_empty_of_empty_interior_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (interior A)) = ∅ → A = (∅ : Set X) := by
  intro hP2 hIntEq
  -- Show `A ⊆ ∅`
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : (x : X) ∈ interior (closure (interior A)) := hP2 hxA
    simpa [hIntEq] using this
  -- The reverse inclusion is trivial.
  have hSub' : (∅ : Set X) ⊆ (A : Set X) := by
    intro x hx
    cases hx
  exact subset_antisymm hSub hSub'

theorem Topology.isClosed_P3_nonempty_implies_interior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → A.Nonempty → (interior A).Nonempty := by
  intro hClosed hP3 hA_nonempty
  rcases hA_nonempty with ⟨x, hxA⟩
  have hx_int : x ∈ interior A := by
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hClosed.closure_eq] using this
  exact ⟨x, hx_int⟩

theorem Topology.P1_implies_eq_empty_of_empty_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior A = ∅ → A = (∅ : Set X) := by
  intro hP1 hIntEq
  -- First, deduce `A ⊆ ∅` from `P1 A` and the hypothesis on the interior.
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : (x : X) ∈ closure (interior A) := hP1 hxA
    simpa [hIntEq, closure_empty] using this
  -- The reverse inclusion is trivial.
  have hSub' : (∅ : Set X) ⊆ (A : Set X) := by
    intro x hx
    cases hx
  exact Set.Subset.antisymm hSub hSub'

theorem Topology.P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) → Topology.P3 A := by
  intro hCl
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hCl, interior_univ] using this

theorem Topology.P1_union_of_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 A → (B ⊆ closure (interior A)) → Topology.P1 (A ∪ B) := by
  intro hP1A hBsub
  intro x hxUnion
  -- We will show that `x` belongs to `closure (interior (A ∪ B))`
  -- by distinguishing the cases `x ∈ A` or `x ∈ B`.
  have hIncl :
      closure (interior A) ⊆ closure (interior (A ∪ B)) := by
    -- First, note that `interior A ⊆ interior (A ∪ B)`.
    have hIntSub : (interior A : Set X) ⊆ interior (A ∪ B) := by
      have hASub : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact interior_mono hASub
    -- Taking closures preserves inclusions.
    exact closure_mono hIntSub
  cases hxUnion with
  | inl hxA =>
      -- Case `x ∈ A`
      have hx_cl : x ∈ closure (interior A) := hP1A hxA
      exact hIncl hx_cl
  | inr hxB =>
      -- Case `x ∈ B`
      have hx_cl : x ∈ closure (interior A) := hBsub hxB
      exact hIncl hx_cl

theorem Topology.dense_implies_P1_P2_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A →
      (Topology.P1 (closure (A : Set X)) ∧
        Topology.P2 (closure (A : Set X)) ∧
        Topology.P3 (closure (A : Set X))) := by
  intro hDense
  exact
    ⟨Topology.dense_implies_P1_closure (A := A) hDense,
      Topology.dense_implies_P2_closure (A := A) hDense,
      Topology.dense_implies_P3_closure (A := A) hDense⟩

theorem Topology.closure_interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆ closure A := by
  -- Step 1: we already know that
  --   `interior (closure (interior A)) ⊆ closure A`.
  have h :
      (interior (closure (interior A)) : Set X) ⊆ closure A :=
    Topology.interior_closure_interior_subset_closure (A := A)
  -- Step 2: taking closures preserves inclusions and `closure (closure A) = closure A`.
  simpa [closure_closure] using closure_mono h

theorem Topology.P2_implies_eq_empty_of_empty_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → interior A = (∅ : Set X) → A = (∅ : Set X) := by
  intro hP2 hIntEq
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.P1_implies_eq_empty_of_empty_interior (A := A) hP1 hIntEq

theorem Topology.closure_interior_iInter_subset_iInter_closure_interior
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    closure (interior (⋂ i, s i : Set X)) ⊆ ⋂ i, closure (interior (s i)) := by
  intro x hx
  -- For each index `i`, we will show `x ∈ closure (interior (s i))`.
  have hx₀ : x ∈ closure (interior (⋂ i, s i : Set X)) := hx
  have hxi : ∀ i, x ∈ closure (interior (s i)) := by
    intro i
    -- `interior (⋂ i, s i)` is contained in `interior (s i)`
    have hsub :
        (interior (⋂ j, s j : Set X) : Set X) ⊆ interior (s i) := by
      -- Since `⋂ j, s j ⊆ s i`, monotonicity of `interior` gives the claim.
      have hSup : (⋂ j, s j : Set X) ⊆ s i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact interior_mono hSup
    -- Taking closures preserves inclusions.
    have hcl :
        closure (interior (⋂ j, s j : Set X)) ⊆ closure (interior (s i)) :=
      closure_mono hsub
    exact hcl hx₀
  -- Combine the pointwise facts into membership in the intersection.
  exact Set.mem_iInter.2 hxi

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure (A : Set X))) := by
  -- First, note that `interior A ⊆ interior (closure A)` because `A ⊆ closure A`.
  have hInt : (interior A : Set X) ⊆ interior (closure (A : Set X)) := by
    have hSub : (A : Set X) ⊆ closure (A : Set X) := subset_closure
    exact interior_mono hSub
  -- Taking closures preserves inclusions, yielding the desired statement.
  exact closure_mono hInt

theorem Topology.P3_union_implies_closure_interior_closure_eq_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B →
      closure (interior (closure (A ∪ B))) = closure (A ∪ B) := by
  intro hP3A hP3B
  have hP3Union : Topology.P3 (A ∪ B) :=
    Topology.P3_union (A := A) (B := B) hP3A hP3B
  exact
    Topology.P3_implies_closure_interior_closure_eq_closure
      (A := A ∪ B) hP3Union

theorem Topology.interior_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = (Set.univ : Set X) ↔ (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- Since `interior A ⊆ A`, the equality `interior A = univ` forces `univ ⊆ A`.
    have hSub : (Set.univ : Set X) ⊆ (A : Set X) := by
      intro x hx
      have : (x : X) ∈ interior (A : Set X) := by
        simpa [hInt] using hx
      exact interior_subset this
    -- The reverse inclusion `A ⊆ univ` is always true.
    have hSub' : (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x hx
      simp
    exact subset_antisymm hSub' hSub
  · intro hA
    simpa [hA, interior_univ] using rfl

theorem Topology.closure_interior_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → closure (interior A) = (Set.univ : Set X) := by
  intro hDenseInt
  simpa using hDenseInt.closure_eq

theorem Topology.P2_closure_interior_iff_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  simpa using (Topology.P2_closure_iff_isOpen_closure (A := interior A))

theorem Topology.isOpen_closure_interior_implies_P2_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior A)) → Topology.P2 (closure (interior A)) := by
  intro hOpen
  exact
    (Topology.P2_closure_interior_iff_isOpen_closure_interior (A := A)).2 hOpen

theorem Topology.dense_interior_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 A := by
  intro hDenseInt
  intro x hxA
  -- `closure (interior A) = univ`
  have hCl_eq_univ : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    hDenseInt.closure_eq
  -- hence `interior (closure (interior A)) = univ`
  have hInt_eq_univ :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hCl_eq_univ, interior_univ]
  -- and so `univ ⊆ interior (closure A)`
  have hSub_univ :
      (Set.univ : Set X) ⊆ interior (closure (A : Set X)) := by
    intro y hy
    have : y ∈ interior (closure (interior (A : Set X))) := by
      simpa [hInt_eq_univ] using hy
    exact
      (Topology.interior_closure_interior_subset_interior_closure (A := A)) this
  -- therefore `interior (closure A) = univ`
  have hIntCl_eq_univ :
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
    apply subset_antisymm
    · intro y hy; simp
    · exact hSub_univ
  -- conclude `x ∈ interior (closure A)`
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hIntCl_eq_univ] using this

theorem Topology.P3_implies_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP3 x hxA
  have : (x : X) ∈ interior (closure (A : Set X)) := hP3 hxA
  exact subset_closure this

theorem Topology.P1_iff_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ A ⊆ closure (interior A) := by
  rfl

theorem Topology.P2_implies_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure A ⊆ closure (interior (closure A)) := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact
    Topology.P3_implies_closure_subset_closure_interior_closure
      (A := A) hP3

theorem Topology.P2_closure_implies_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP2Cl
  exact (Topology.P2_closure_iff_isOpen_closure (A := A)).1 hP2Cl

theorem Topology.P2_implies_eq_empty_of_empty_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (A : Set X)) = ∅ → A = (∅ : Set X) := by
  intro hP2 hIntEq
  -- From `P2`, derive `P3`.
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  -- Apply the corresponding result for `P3`.
  exact
    Topology.P3_implies_eq_empty_of_empty_interior_closure
      (A := A) hP3 hIntEq

theorem Topology.P3_of_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = (Set.univ : Set X) → Topology.P3 A := by
  intro hIntEq
  intro x hxA
  -- `x` lies in `interior A` because `interior A = univ`.
  have hxIntA : x ∈ interior (A : Set X) := by
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hIntEq] using this
  -- Monotonicity of `interior` for the inclusion `A ⊆ closure A`.
  have hSubset :
      (interior (A : Set X) : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hSubset hxIntA

theorem Topology.interior_closure_iInter_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    interior (closure (⋂ i, s i : Set X)) ⊆ ⋂ i, interior (closure (s i)) := by
  intro x hx
  -- For each index `i`, we show that `x` belongs to `interior (closure (s i))`.
  have h : ∀ i, x ∈ interior (closure (s i)) := by
    intro i
    -- Since `⋂ j, s j ⊆ s i`, the same holds after taking closures and interiors.
    have hSub : (⋂ j, s j : Set X) ⊆ s i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have hCl : closure (⋂ j, s j : Set X) ⊆ closure (s i) :=
      closure_mono hSub
    have hInt :
        interior (closure (⋂ j, s j : Set X)) ⊆ interior (closure (s i)) :=
      interior_mono hCl
    exact hInt hx
  -- Combine the pointwise facts into membership in the intersection.
  exact Set.mem_iInter.2 h

theorem Topology.P3_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P3 A := by
  intro hClIntEq
  intro x _
  -- First, note that `interior (closure (interior A)) = univ`.
  have hIntEq : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [hClIntEq, interior_univ] using congrArg interior hClIntEq
  -- Hence every point lies in `interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := by
    simpa [hIntEq] using (by simp : x ∈ (Set.univ : Set X))
  -- Use monotonicity to pass to `interior (closure A)`.
  have hsubset :
      interior (closure (interior A)) ⊆ interior (closure (A : Set X)) :=
    Topology.interior_closure_interior_subset_interior_closure (A := A)
  exact hsubset hxInt

theorem Topology.closure_interior_closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First collapse the two outermost `closure ∘ interior` cycles.
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior (closure (interior A))))) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (A := closure (interior (closure (interior (closure (interior A)))))))
  -- Next collapse the remaining three–cycle, using the already-established idempotency.
  have h₂ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior A) :=
    Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior (A := A)
  -- Put the two reductions together.
  simpa [h₁] using h₂

theorem Topology.isClosed_P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hClosed hP1 hP3
  -- `IsOpen A` follows from the characterisation for closed sets.
  have hOpen : IsOpen A := by
    have hEquiv := (Topology.isClosed_isOpen_iff_P1_and_P3 (A := A) hClosed)
    exact (hEquiv).mpr ⟨hP1, hP3⟩
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (A := A) hOpen

theorem Topology.P2_implies_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → (A : Set X) ⊆ closure (interior A) := by
  intro hP2 x hxA
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact hP1 hxA

theorem Topology.P1_implies_frontier_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → frontier (A : Set X) ⊆ closure (interior A) := by
  intro hP1 x hxFrontier
  -- `x` lies in `closure A` by definition of the frontier.
  have hx_closureA : (x : X) ∈ closure (A : Set X) := hxFrontier.1
  -- From `P1 A`, `closure A` is contained in `closure (interior A)`.
  have hsubset : (closure (A : Set X)) ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  exact hsubset hx_closureA

theorem Topology.P2_implies_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure (A : Set X)) := by
  intro hP2
  have h :=
    Topology.P2_implies_closure_interior_closure_eq_closure (A := A) hP2
  simpa using congrArg interior h

theorem Topology.P1_of_subset_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hBsub : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  intro x hxB
  -- Step 1: from the assumption `B ⊆ closure (interior A)` obtain
  --         that `x` lies in `closure (interior A)`.
  have hx_clA : x ∈ closure (interior A) := hBsub hxB
  -- Step 2: monotonicity of `interior` for the inclusion `A ⊆ B`.
  have hInt : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Step 3: taking closures preserves inclusions.
  have hCl : (closure (interior A) : Set X) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Step 4: combine the facts to obtain the desired conclusion.
  exact hCl hx_clA

theorem Topology.P2_implies_frontier_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → frontier (A : Set X) ⊆ closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact
    Topology.P1_implies_frontier_subset_closure_interior (A := A) hP1

theorem Topology.dense_interior_implies_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) →
      (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  intro hDense
  exact
    ⟨Topology.dense_interior_implies_P1 (A := A) hDense,
      Topology.dense_interior_implies_P2 (A := A) hDense,
      Topology.dense_interior_implies_P3 (A := A) hDense⟩

theorem Topology.isOpen_iUnion_implies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, IsOpen (s i)) →
      (Topology.P1 (⋃ i, s i) ∧
        Topology.P2 (⋃ i, s i) ∧ Topology.P3 (⋃ i, s i)) := by
  intro hOpen
  have hP1 : Topology.P1 (⋃ i, s i) :=
    Topology.isOpen_iUnion_implies_P1 (s := s) hOpen
  have hP2 : Topology.P2 (⋃ i, s i) :=
    Topology.isOpen_iUnion_implies_P2 (s := s) hOpen
  have hP3 : Topology.P3 (⋃ i, s i) :=
    Topology.isOpen_iUnion_implies_P3 (s := s) hOpen
  exact And.intro hP1 (And.intro hP2 hP3)

theorem Topology.P3_implies_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      interior (closure (interior (closure A))) = interior (closure A) := by
  intro hP3
  have h :=
    Topology.P3_implies_closure_interior_closure_eq_closure (A := A) hP3
  simpa using congrArg interior h

theorem Topology.frontier_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ⊆ closure (A : Set X) := by
  intro x hx
  exact hx.1

theorem Topology.interior_inter_isOpen_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B : Set X) = interior A ∩ B := by
  simpa [Set.inter_comm] using
    (Topology.interior_inter_isOpen_left (A := B) (B := A) hB)

theorem Topology.P3_implies_frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      frontier (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP3 x hxFrontier
  -- A point in the frontier of `A` lies in `closure A`.
  have hx_closureA : (x : X) ∈ closure (A : Set X) := hxFrontier.1
  -- `closure A` is contained in `closure (interior (closure A))` by `P3`.
  have hsubset :
      (closure (A : Set X)) ⊆ closure (interior (closure (A : Set X))) :=
    Topology.P3_implies_closure_subset_closure_interior_closure (A := A) hP3
  exact hsubset hx_closureA

theorem Topology.frontier_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → frontier (closure (A : Set X)) = (∅ : Set X) := by
  intro hDense
  simpa [hDense.closure_eq, frontier_univ]

theorem Topology.dense_implies_interior_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A →
      interior (closure (interior (closure (A : Set X)))) = (Set.univ : Set X) := by
  intro hDense
  have h :=
    Topology.dense_interior_closure_eq_univ (A := A) hDense
  simpa [interior_univ] using congrArg interior h

theorem Topology.isOpen_closure_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hOpenCl
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.isClosed_isOpen_implies_closure_interior_eq_self
        (A := closure (A : Set X)) hClosed hOpenCl)

theorem Topology.P2_iff_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A ↔ A ⊆ interior (closure (interior A)) := by
  rfl

theorem Topology.closure_interior_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.isClosed_isOpen_implies_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → IsOpen A → (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  intro hClosed hOpen
  have hEquiv := (Topology.isClosed_isOpen_iff_P1_P2_P3 (A := A) hClosed)
  exact (hEquiv).1 hOpen

theorem Topology.interior_eq_self_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (A : Set X) → Topology.P1 A := by
  intro hIntEq
  -- From `interior A = A`, we deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (isOpen_iff_interior_eq (A := A)).2 hIntEq
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (A := A) hOpen

theorem Topology.closure_subset_of_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hSub : (A : Set X) ⊆ closure (B : Set X))
    (hClosed : IsClosed (B : Set X)) :
    closure (A : Set X) ⊆ (B : Set X) := by
  -- `closure A` is contained in the closure of `closure B`.
  have h₁ : closure (A : Set X) ⊆ closure (closure (B : Set X)) :=
    closure_mono hSub
  -- Since `B` is closed, `closure B = B`.
  simpa [closure_closure, hClosed.closure_eq] using h₁

theorem Topology.P1_implies_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure A) := by
  intro hP1
  have h :=
    Topology.P1_implies_closure_interior_closure_eq_closure (A := A) hP1
  simpa using congrArg interior h

theorem Topology.isClosed_P3_implies_closure_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → closure (interior A) = A := by
  intro hClosed hP3
  -- From the assumptions we obtain `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.isClosed_P3_implies_P1 (A := A) hClosed hP3
  -- Apply the existing result for closed sets with property `P1`.
  exact
    Topology.isClosed_P1_implies_closure_interior_eq_self
      (A := A) hClosed hP1



theorem Topology.interior_closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆ closure A := by
  intro x hx
  -- `x` lies in the closure of `interior (closure A)`.
  have hx₁ : x ∈ closure (interior (closure (A : Set X))) :=
    interior_subset hx
  -- `interior (closure A)` itself is contained in `closure A`.
  have hIntSub : (interior (closure (A : Set X)) : Set X) ⊆ closure A := by
    intro y hy
    exact interior_subset hy
  -- Taking closures preserves inclusions.
  have hClSub :
      closure (interior (closure (A : Set X))) ⊆ closure (closure (A : Set X)) :=
    closure_mono hIntSub
  -- Simplify the right‐hand closure.
  have hSub : (closure (interior (closure (A : Set X))) : Set X) ⊆ closure A := by
    simpa [closure_closure] using hClSub
  exact hSub hx₁

theorem Topology.frontier_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior (A : Set X)) ⊆ closure (A : Set X) := by
  intro x hx
  -- First, use the general fact `frontier S ⊆ closure S` with `S := interior A`.
  have hx₁ : x ∈ closure (interior (A : Set X)) :=
    (Topology.frontier_subset_closure (A := interior A)) hx
  -- Next, `closure (interior A)` is contained in `closure A`.
  have hsubset : (closure (interior (A : Set X)) : Set X) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  -- Combining the two inclusions yields the desired result.
  exact hsubset hx₁

theorem Topology.closure_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier (A : Set X)) ⊆ closure (A : Set X) := by
  -- First, we recall the inclusion `frontier A ⊆ closure A`.
  have h : (frontier (A : Set X) : Set X) ⊆ closure (A : Set X) :=
    Topology.frontier_subset_closure (A := A)
  -- Taking closures preserves inclusions; simplify with `closure_closure`.
  simpa [closure_closure] using closure_mono h

theorem Topology.dense_isClosed_implies_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsClosed A → (A : Set X) = (Set.univ : Set X) := by
  intro hDense hClosed
  simpa [hClosed.closure_eq] using hDense.closure_eq

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- `A ∩ B ⊆ A` and `A ∩ B ⊆ B`
  have hSubA : ((A ∩ B) : Set X) ⊆ (A : Set X) := by
    intro y hy
    exact hy.1
  have hSubB : ((A ∩ B) : Set X) ⊆ (B : Set X) := by
    intro y hy
    exact hy.2
  -- Taking closures preserves inclusions.
  have hClA : closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) :=
    closure_mono hSubA
  have hClB : closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) :=
    closure_mono hSubB
  exact And.intro (hClA hx) (hClB hx)

theorem Topology.P1_of_frontier_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) ⊆ closure (interior A) → Topology.P1 A := by
  intro hFrontier
  intro x hxA
  by_cases hx_int : x ∈ interior A
  · exact subset_closure hx_int
  ·
    have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
    have hx_frontier : x ∈ frontier (A : Set X) := by
      exact And.intro hx_closure hx_int
    exact hFrontier hx_frontier

theorem Topology.isClosed_P3_implies_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → interior A = A := by
  intro hClosed hP3
  -- We already have `interior (closure A) = A` under the same hypotheses.
  have h :=
    Topology.isClosed_P3_implies_interior_closure_eq_self
      (A := A) hClosed hP3
  -- Since `A` is closed, `closure A = A`; rewriting yields the desired equality.
  simpa [hClosed.closure_eq] using h

theorem Topology.closure_interior_closure_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure (A : Set X)))) =
      closure (interior (closure (A : Set X))) := by
  simpa [closure_closure]

theorem Topology.P2_implies_closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- From `P2`, we know both `closure (interior (closure A)) = closure A`
  -- and `closure (interior A) = closure A`.
  have h₁ :=
    Topology.P2_implies_closure_interior_closure_eq_closure (A := A) hP2
  have h₂ :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Rearrange `h₂` to match the direction needed for the calculation.
  have h₃ : closure A = closure (interior A) := by
    simpa using h₂.symm
  calc
    closure (interior (closure A)) = closure A := h₁
    _ = closure (interior A) := h₃



theorem Topology.P3_iff_forall_open_nbhd_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔
      ∀ x : X, x ∈ (A : Set X) →
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (A : Set X) := by
  constructor
  · intro hP3 x hxA
    -- Choose the canonical open neighbourhood `interior (closure A)`.
    have hx_int : x ∈ interior (closure (A : Set X)) := hP3 hxA
    exact
      ⟨interior (closure (A : Set X)), isOpen_interior, hx_int, interior_subset⟩
  · intro h
    intro x hxA
    -- Extract an open neighbourhood of `x` contained in `closure A`.
    rcases h x hxA with ⟨U, hOpenU, hxU, hU_sub⟩
    -- This witnesses that `x` is in the interior of `closure A`.
    have : (∃ V : Set X, V ⊆ closure (A : Set X) ∧ IsOpen V ∧ x ∈ V) :=
      ⟨U, hU_sub, hOpenU, hxU⟩
    simpa [mem_interior] using this

theorem Topology.isClosed_P2_implies_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → Topology.P2 A → frontier (A : Set X) = (∅ : Set X) := by
  intro hClosed hP2
  -- From the premises, `A` is both closed and open.
  have hOpen : IsOpen (A : Set X) :=
    Topology.isClosed_P2_implies_isOpen (A := A) hClosed hP2
  -- Hence `closure A = A` and `interior A = A`.
  have hCl : closure (A : Set X) = A := hClosed.closure_eq
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  -- Unfold `frontier` and simplify.
  ext x
  simp [frontier, hCl, hInt]

theorem Topology.frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior (A : Set X)) ⊆ frontier A := by
  intro x hx
  -- Unpack the definition of the frontier of `interior A`.
  rcases hx with ⟨hx_closureInt, hx_not_intInt⟩
  -- `closure (interior A)` is contained in `closure A`.
  have hsubset : (closure (interior (A : Set X)) : Set X) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  -- Assemble the two conditions defining `x ∈ frontier A`.
  refine And.intro (hsubset hx_closureInt) ?_
  -- Rewrite `x ∉ interior (interior A)` as `x ∉ interior A`.
  simpa [interior_interior] using hx_not_intInt

theorem Topology.dense_isClosed_implies_frontier_eq_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense A → IsClosed A → frontier (A : Set X) = (∅ : Set X) := by
  intro hDense hClosed
  have hA : (A : Set X) = (Set.univ : Set X) :=
    Topology.dense_isClosed_implies_univ (A := A) hDense hClosed
  simpa [hA, frontier_univ]

theorem Topology.isClosed_isOpen_implies_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed (A : Set X) → IsOpen A → frontier (A : Set X) = (∅ : Set X) := by
  intro hClosed hOpen
  -- Any open set satisfies `P2`.
  have hP2 : Topology.P2 A := Topology.isOpen_implies_P2 (A := A) hOpen
  -- Apply the closed‐plus‐`P2` lemma.
  exact Topology.isClosed_P2_implies_frontier_eq_empty (A := A) hClosed hP2

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hxInt
  exact subset_closure (interior_subset hxInt)

theorem Topology.P2_iff_forall_open_nbhd_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A ↔
      ∀ x : X, x ∈ (A : Set X) →
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A) := by
  constructor
  · intro hP2 x hxA
    refine
      ⟨interior (closure (interior A)), isOpen_interior,
        ?_, interior_subset⟩
    exact hP2 hxA
  · intro h
    intro x hxA
    rcases h x hxA with ⟨U, hOpenU, hxU, hU_sub⟩
    have hU_sub_int :
        (U : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal hU_sub hOpenU
    exact hU_sub_int hxU

theorem Topology.closure_inter_interiors_subset_inter_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior A ∩ interior B) : Set X) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior A ∩ interior B` is contained in each of `interior A`, `interior B`.
  have hSubA : (interior A ∩ interior B : Set X) ⊆ interior A := by
    intro y hy; exact hy.1
  have hSubB : (interior A ∩ interior B : Set X) ⊆ interior B := by
    intro y hy; exact hy.2
  -- Taking closures preserves inclusions.
  have hClA :
      closure ((interior A ∩ interior B) : Set X) ⊆ closure (interior A) :=
    closure_mono hSubA
  have hClB :
      closure ((interior A ∩ interior B) : Set X) ⊆ closure (interior B) :=
    closure_mono hSubB
  exact And.intro (hClA hx) (hClB hx)

theorem Topology.P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
      Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  exact Topology.isOpen_implies_P1_P2_P3 (A := Set.univ) hOpen

theorem Topology.P2_implies_frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      frontier (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact
    Topology.P3_implies_frontier_subset_closure_interior_closure
      (A := A) hP3



theorem Topology.P1_of_P3_and_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (closure A ⊆ closure (interior A)) → Topology.P1 A := by
  intro hP3 hClSub
  intro x hxA
  -- From `P3`, the point `x` lies in `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure A) := hP3 hxA
  -- We will show that `interior (closure A) ⊆ closure (interior A)`.
  have hIncl : (interior (closure A) : Set X) ⊆ closure (interior A) := by
    -- `interior (closure A)` is contained in `closure A`.
    have h₁ : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    -- Chain the inclusions using the hypothesis `closure A ⊆ closure (interior A)`.
    exact Set.Subset.trans h₁ hClSub
  -- Applying the inclusion to `x` gives the desired conclusion.
  exact hIncl hxIntCl

theorem Topology.P1_implies_closure_interior_closure_eq_closure_interior_simple
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      closure (interior (closure (A : Set X))) = closure (interior A) := by
  intro hP1
  -- First, rewrite `closure (interior (closure A))` using `P1 A`.
  have h₁ := Topology.P1_implies_closure_interior_closure_eq_closure (A := A) hP1
  -- Next, rewrite `closure A` in terms of `closure (interior A)`.
  have h₂ := Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  simpa [h₂.symm] using h₁



theorem Topology.subset_closure_interior_of_subset_of_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 A → B ⊆ A → B ⊆ closure (interior A) := by
  intro hP1 hSub x hxB
  exact hP1 (hSub hxB)

theorem Topology.isOpen_closure_implies_frontier_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      frontier (closure (A : Set X)) = (∅ : Set X) := by
  intro hOpen
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  simp [frontier, hInt, closure_closure, Set.diff_self]

theorem Topology.P1_of_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (A : Set X)) ⊆ closure (interior A) → Topology.P1 A := by
  intro hSub
  intro x hxA
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  exact hSub hx_cl

theorem Topology.isClosed_P3_implies_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → Topology.P3 A → frontier (A : Set X) = (∅ : Set X) := by
  intro hClosed hP3
  have hOpen : IsOpen (A : Set X) :=
    Topology.isClosed_P3_implies_isOpen (A := A) hClosed hP3
  exact Topology.isClosed_isOpen_implies_frontier_eq_empty (A := A) hClosed hOpen

theorem Topology.isOpen_closure_implies_P1_P2_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      (Topology.P1 (closure (A : Set X)) ∧
        Topology.P2 (closure (A : Set X)) ∧
        Topology.P3 (closure (A : Set X))) := by
  intro hOpen
  have hP1 : Topology.P1 (closure (A : Set X)) :=
    Topology.isOpen_closure_implies_P1_closure (A := A) hOpen
  have hP2 : Topology.P2 (closure (A : Set X)) :=
    Topology.isOpen_closure_implies_P2_closure (A := A) hOpen
  have hP3 : Topology.P3 (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen_closure (A := A)).2 hOpen
  exact And.intro hP1 (And.intro hP2 hP3)

theorem Topology.P1_of_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = (Set.univ : Set X) → Topology.P1 A := by
  intro hIntEq
  intro x hxA
  -- Any point lies in `interior A` because `interior A = univ`.
  have hxInt : (x : X) ∈ interior (A : Set X) := by
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hIntEq] using this
  -- Hence it lies in `closure (interior A)`.
  exact subset_closure hxInt

theorem Topology.interior_union_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = interior A ∪ interior B := by
  -- Evaluate the interiors of the open sets `A` and `B`.
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  -- The union of two open sets is open, so its interior is itself.
  have hIntUnion : interior (A ∪ B : Set X) = A ∪ B :=
    (hA.union hB).interior_eq
  -- Rewrite everything using the computed equalities.
  simpa [hIntA, hIntB, hIntUnion]

theorem Topology.P1_implies_frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      frontier (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP1 x hxFrontier
  -- `x` lies in the closure of `A` by definition of the frontier.
  have hx_closureA : (x : X) ∈ closure (A : Set X) := hxFrontier.1
  -- From `P1 A`, `closure A ⊆ closure (interior A)`.
  have hSub₁ :
      (closure (A : Set X)) ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  have hx_closureIntA : x ∈ closure (interior A) := hSub₁ hx_closureA
  -- And `closure (interior A)` is contained in
  -- `closure (interior (closure A))`.
  have hSub₂ :
      (closure (interior A)) ⊆
        closure (interior (closure (A : Set X))) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  exact hSub₂ hx_closureIntA

theorem Topology.P1_nonempty_implies_interior_closure_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP1 hA_nonempty
  -- Obtain a point in `interior A` using the existing lemma.
  have hIntA : (interior A).Nonempty :=
    Topology.P1_nonempty_implies_interior_nonempty (A := A) hP1 hA_nonempty
  rcases hIntA with ⟨x, hxIntA⟩
  -- Since `interior A ⊆ interior (closure A)`, the same point lies in
  -- `interior (closure A)`.
  have hsubset :
      (interior A : Set X) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  exact ⟨x, hsubset hxIntA⟩

theorem Topology.frontier_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (closure (A : Set X)) ⊆ closure (A : Set X) := by
  -- Apply the general inclusion `frontier S ⊆ closure S` to `S = closure A`.
  have h :
      frontier (closure (A : Set X)) ⊆ closure (closure (A : Set X)) :=
    Topology.frontier_subset_closure (A := closure (A : Set X))
  simpa [closure_closure] using h

theorem interior_closure_interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  intro x hx
  have h_closure_subset : (closure (interior A) : Set X) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  exact (interior_mono h_closure_subset) hx

theorem Topology.P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ (closure (A : Set X) ⊆ closure (interior A)) := by
  constructor
  · intro hP1
    exact
      Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  · intro hSub
    exact
      Topology.P1_of_closure_subset_closure_interior (A := A) hSub

theorem Topology.iUnion_interior_closure_subset_interior_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (⋃ i, interior (closure (s i))) ⊆ interior (closure (⋃ i, s i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `closure (s i)` is contained in `closure (⋃ j, s j)`.
  have hcl : closure (s i) ⊆ closure (⋃ j, s j) := by
    have hSub : (s i : Set X) ⊆ ⋃ j, s j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono hSub
  -- Applying monotonicity of `interior` to the inclusion of closures.
  have hInt :
      interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) :=
    interior_mono hcl
  exact hInt hx_i

theorem Topology.interior_iInter_subset_iInter_interior
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    interior (⋂ i, s i : Set X) ⊆ ⋂ i, interior (s i) := by
  intro x hx
  -- For each index `i`, we will show that `x ∈ interior (s i)`.
  have h : ∀ i, x ∈ interior (s i) := by
    intro i
    -- Since `⋂ j, s j ⊆ s i`, monotonicity of `interior` yields the claim.
    have hSub : (⋂ j, s j : Set X) ⊆ s i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have hInt : interior (⋂ j, s j : Set X) ⊆ interior (s i) :=
      interior_mono hSub
    exact hInt hx
  -- Combine the pointwise facts into membership of the intersection.
  exact Set.mem_iInter.2 h

theorem Topology.isOpen_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → interior (closure (interior A)) = interior (closure A) := by
  intro hOpen
  -- Any open set satisfies property `P2`.
  have hP2 : Topology.P2 A := Topology.isOpen_implies_P2 (A := A) hOpen
  -- Apply the equality furnished by `P2`.
  exact
    Topology.P2_implies_interior_closure_interior_eq_interior_closure
      (A := A) hP2

theorem Topology.interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆
      closure (interior (closure (A : Set X))) := by
  intro x hx
  exact subset_closure hx

theorem Topology.P2_of_P3_and_closure_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A ⊆ closure (interior A) → Topology.P2 A := by
  intro hP3 hClSub
  -- From the assumptions, obtain `P1 A` using the existing lemma.
  have hP1 : Topology.P1 A :=
    Topology.P1_of_P3_and_closure_subset (A := A) hP3 hClSub
  -- Combine `P1 A` and `P3 A` to deduce `P2 A`.
  exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3

theorem Topology.frontier_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier ((A ∩ B) : Set X) ⊆ frontier (A : Set X) ∪ frontier (B : Set X) := by
  classical
  intro x hx
  -- `hx` states that `x` is in the frontier of `A ∩ B`.
  rcases hx with ⟨hClAB, hNotIntAB⟩
  -- A point in the closure of `A ∩ B` lies in the closures of both `A` and `B`.
  have hClSubset :
      closure ((A ∩ B) : Set X) ⊆
        closure (A : Set X) ∩ closure (B : Set X) :=
    Topology.closure_inter_subset_inter_closure (A := A) (B := B)
  have hClA : x ∈ closure (A : Set X) := (hClSubset hClAB).1
  have hClB : x ∈ closure (B : Set X) := (hClSubset hClAB).2
  -- Case distinction on membership of `x` in the interiors of `A` and `B`.
  by_cases hIntA : x ∈ interior (A : Set X)
  · by_cases hIntB : x ∈ interior (B : Set X)
    · -- If `x` is in both interiors, it is in the interior of `A ∩ B`,
      -- contradicting `hNotIntAB`.
      have hInInter :
          x ∈ interior (A : Set X) ∩ interior (B : Set X) :=
        And.intro hIntA hIntB
      have hIntAB : x ∈ interior ((A ∩ B) : Set X) :=
        (interior_inter_subset (A := A) (B := B)) hInInter
      exact (hNotIntAB hIntAB).elim
    · -- `x` is not in `interior B`, hence in the frontier of `B`.
      have hFrontB : x ∈ frontier (B : Set X) := And.intro hClB hIntB
      exact Or.inr hFrontB
  · -- `x` is not in `interior A`; similar reasoning yields membership
    -- in the frontier of `A` or `B`.
    by_cases hIntB : x ∈ interior (B : Set X)
    · -- `x` is not in `interior A` but is in `interior B`, so it belongs
      -- to the frontier of `A`.
      have hFrontA : x ∈ frontier (A : Set X) := And.intro hClA hIntA
      exact Or.inl hFrontA
    · -- `x` is in neither interior; choose either frontier (here, of `A`).
      have hFrontA : x ∈ frontier (A : Set X) := And.intro hClA hIntA
      exact Or.inl hFrontA

theorem Topology.frontier_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier ((A ∪ B) : Set X) ⊆ frontier (A : Set X) ∪ frontier (B : Set X) := by
  intro x hx
  rcases hx with ⟨hx_closureUnion, hx_not_intUnion⟩
  -- `x` is in the closure of `A` or of `B` (since `closure (A ∪ B) = closure A ∪ closure B`)
  have hClosure : x ∈ closure (A : Set X) ∨ x ∈ closure (B : Set X) := by
    have h : x ∈ closure (A : Set X) ∪ closure (B : Set X) := by
      simpa [closure_union] using hx_closureUnion
    simpa [Set.mem_union] using h
  -- Analyse the two cases.
  cases hClosure with
  | inl hx_closureA =>
      -- Case: `x ∈ closure A`
      by_cases hx_intA : x ∈ interior (A : Set X)
      · -- If `x` were in `interior A`, it would be in `interior (A ∪ B)`, contradiction.
        have hsubset :
            interior (A : Set X) ∪ interior (B : Set X) ⊆
              interior ((A ∪ B) : Set X) :=
          interior_union (A := A) (B := B)
        have hx_intUnion : x ∈ interior ((A ∪ B) : Set X) :=
          hsubset (Or.inl hx_intA)
        have hFalse : False := hx_not_intUnion hx_intUnion
        exact False.elim hFalse
      · -- Otherwise, `x` is not in `interior A`; hence `x ∈ frontier A`.
        exact Or.inl (And.intro hx_closureA hx_intA)
  | inr hx_closureB =>
      -- Case: `x ∈ closure B`
      by_cases hx_intB : x ∈ interior (B : Set X)
      · -- If `x` were in `interior B`, it would be in `interior (A ∪ B)`, contradiction.
        have hsubset :
            interior (A : Set X) ∪ interior (B : Set X) ⊆
              interior ((A ∪ B) : Set X) :=
          interior_union (A := A) (B := B)
        have hx_intUnion : x ∈ interior ((A ∪ B) : Set X) :=
          hsubset (Or.inr hx_intB)
        have hFalse : False := hx_not_intUnion hx_intUnion
        exact False.elim hFalse
      · -- Otherwise, `x` is not in `interior B`; hence `x ∈ frontier B`.
        exact Or.inr (And.intro hx_closureB hx_intB)

theorem Topology.dense_interior_implies_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → closure (interior A) = closure A := by
  intro hDense
  -- `closure (interior A)` is the whole space.
  have hUniv : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- One inclusion is monotonicity of `closure`.
  have h₁ :
      (closure (interior (A : Set X)) : Set X) ⊆ closure A :=
    closure_mono (interior_subset : (interior (A : Set X) : Set X) ⊆ A)
  -- The other inclusion is trivial after rewriting with `hUniv`.
  have h₂ :
      (closure (A : Set X)) ⊆ closure (interior (A : Set X)) := by
    intro x hx
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [hUniv] using this
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.isOpen_P1_iff_P2_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A)) := by
  intro hOpen
  -- Auxiliary equivalences for an open set.
  have hP1P2 := (Topology.isOpen_P1_iff_P2 (A := A) hOpen)
  have hP1P3 := (Topology.isOpen_P1_iff_P3 (A := A) hOpen)
  constructor
  · intro hP1
    -- From `P1`, obtain `P2` and `P3` via the auxiliary equivalences.
    exact And.intro ((hP1P2).1 hP1) ((hP1P3).1 hP1)
  · rintro ⟨hP2, _hP3⟩
    -- Recover `P1` from `P2` using the equivalence for open sets.
    exact (hP1P2).2 hP2

theorem Topology.interior_iUnion_of_isOpen {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} :
    (∀ i, IsOpen (s i)) →
      interior (⋃ i, s i : Set X) = ⋃ i, interior (s i) := by
  intro hOpen
  -- The union of the open sets is open.
  have hOpenUnion : IsOpen (⋃ i, s i : Set X) :=
    isOpen_iUnion (fun i => hOpen i)
  -- Hence its interior is itself.
  have h₁ : interior (⋃ i, s i : Set X) = (⋃ i, s i : Set X) :=
    hOpenUnion.interior_eq
  -- Rewrite each `s i` by `interior (s i)` (they coincide because `s i` is open).
  have h₂ : (⋃ i, s i : Set X) = ⋃ i, interior (s i) := by
    classical
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      have : x ∈ interior (s i) := by
        simpa [(hOpen i).interior_eq] using hx_i
      exact Set.mem_iUnion.2 ⟨i, this⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      have : x ∈ s i :=
        (interior_subset : interior (s i) ⊆ s i) hx_i
      exact Set.mem_iUnion.2 ⟨i, this⟩
  simpa [h₂] using h₁

theorem Topology.frontier_eq_closure_diff_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (A : Set X) → frontier (A : Set X) = closure (A : Set X) \ A := by
  intro hOpen
  simpa [frontier, hOpen.interior_eq]

theorem Topology.frontier_eq_self_diff_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → frontier (A : Set X) = A \ interior A := by
  intro hClosed
  simpa [frontier, hClosed.closure_eq]

theorem Topology.frontier_eq_empty_iff_isClosed_and_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) ↔ (IsClosed A ∧ IsOpen A) := by
  classical
  constructor
  · intro hFrontier
    -- First, show `closure A ⊆ interior A`.
    have hSub : (closure (A : Set X) : Set X) ⊆ interior A := by
      intro x hxCl
      by_cases hxInt : x ∈ interior (A : Set X)
      · exact hxInt
      ·
        -- Otherwise, `x` lies in the frontier, contradicting `frontier A = ∅`.
        have hxFront : x ∈ frontier (A : Set X) := And.intro hxCl hxInt
        have : x ∈ (∅ : Set X) := by
          simpa [hFrontier] using hxFront
        cases this
    -- From the inclusions `interior A ⊆ A ⊆ closure A` and `closure A ⊆ interior A`,
    -- deduce the equalities needed for openness and closedness.
    have hIntEq : interior (A : Set X) = A := by
      apply subset_antisymm
      · exact interior_subset
      · intro x hxA
        have : x ∈ closure (A : Set X) := subset_closure hxA
        exact hSub this
    have hClEq : closure (A : Set X) = A := by
      apply subset_antisymm
      · intro x hxCl
        have : x ∈ interior (A : Set X) := hSub hxCl
        exact interior_subset this
      · exact subset_closure
    -- Conclude that `A` is both closed and open.
    have hClosed : IsClosed (A : Set X) := by
      simpa [hClEq] using (isClosed_closure : IsClosed (closure (A : Set X)))
    have hOpen : IsOpen (A : Set X) := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using this
    exact And.intro hClosed hOpen
  · rintro ⟨hClosed, hOpen⟩
    -- Use `closure A = A` and `interior A = A` to rewrite the frontier.
    have hClEq : closure (A : Set X) = A := hClosed.closure_eq
    have hIntEq : interior (A : Set X) = A := hOpen.interior_eq
    simpa [frontier, hClEq, hIntEq, Set.diff_self]

theorem Topology.closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior (B : Set X)) ⊆
      closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- `A ∩ interior B ⊆ A`
  have hSubA : (A ∩ interior (B : Set X) : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  -- `A ∩ interior B ⊆ B` (because `interior B ⊆ B`)
  have hSubB : (A ∩ interior (B : Set X) : Set X) ⊆ B := by
    intro y hy
    exact (interior_subset : interior (B : Set X) ⊆ B) hy.2
  -- Taking closures preserves inclusions.
  have hxA : x ∈ closure (A : Set X) := (closure_mono hSubA) hx
  have hxB : x ∈ closure (B : Set X) := (closure_mono hSubB) hx
  exact And.intro hxA hxB

theorem Topology.closure_frontier_eq_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier (A : Set X)) = frontier (A : Set X) := by
  have hClosed : IsClosed (frontier (A : Set X)) := isClosed_frontier
  simpa using hClosed.closure_eq

theorem Topology.closure_subset_closure_interior_of_frontier_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (interior A) →
      closure (A : Set X) ⊆ closure (interior A) := by
  intro hFront x hxCl
  by_cases hxInt : x ∈ interior (A : Set X)
  · -- If `x` is already in `interior A`, the result is immediate.
    exact subset_closure hxInt
  · -- Otherwise, `x` lies in the frontier of `A`, hence in the target by `hFront`.
    have hxFront : x ∈ frontier (A : Set X) := by
      exact And.intro hxCl hxInt
    exact hFront hxFront



theorem Topology.P1_iUnion_implies_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P1 (s i)) →
      closure (interior (⋃ i, s i : Set X)) = closure (⋃ i, s i : Set X) := by
  intro hP1
  -- First, the union itself satisfies `P1`.
  have hP1Union : Topology.P1 (⋃ i, s i) :=
    Topology.P1_iUnion (s := s) hP1
  -- Apply the characterisation of `P1` in terms of closures.
  exact
    Topology.P1_implies_closure_interior_eq_closure
      (A := ⋃ i, s i) hP1Union

theorem Topology.frontier_subset_closure_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (Aᶜ : Set X) := by
  intro x hxFront
  rcases hxFront with ⟨hxClA, hxNotIntA⟩
  by_cases hmem : x ∈ closure (Aᶜ : Set X)
  · exact hmem
  ·
    -- `x` lies in the open set `U = (closure Aᶜ)ᶜ`.
    have hxInU : x ∈ (closure (Aᶜ : Set X))ᶜ := by
      have : x ∉ closure (Aᶜ : Set X) := hmem
      simpa [Set.mem_compl] using this
    have hOpenU : IsOpen ((closure (Aᶜ : Set X))ᶜ) :=
      (isClosed_closure (s := (Aᶜ : Set X))).isOpen_compl
    -- Show that `U ⊆ A`.
    have hU_sub_A : ((closure (Aᶜ : Set X))ᶜ : Set X) ⊆ A := by
      intro y hyU
      by_contra hNotA
      -- From `y ∉ A`, deduce `y ∈ Aᶜ`.
      have hyInCompl : (y : X) ∈ (Aᶜ : Set X) := by
        simpa [Set.mem_compl] using hNotA
      -- Hence `y ∈ closure Aᶜ`, contradicting `hyU`.
      have hyInClos : y ∈ closure (Aᶜ : Set X) := subset_closure hyInCompl
      have : y ∉ closure (Aᶜ : Set X) := by
        simpa [Set.mem_compl] using hyU
      exact (this hyInClos).elim
    -- `U` is an open neighbourhood of `x` contained in `A`, so `x ∈ interior A`.
    have hxIntA : x ∈ interior (A : Set X) := by
      have hU_sub_intA :
          ((closure (Aᶜ : Set X))ᶜ : Set X) ⊆ interior (A : Set X) :=
        interior_maximal hU_sub_A hOpenU
      exact hU_sub_intA hxInU
    exact (hxNotIntA hxIntA).elim

theorem Topology.dense_subset_closed_eq_univ {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hDense : Dense (A : Set X)) (hClosed : IsClosed (B : Set X))
    (hSub : (A : Set X) ⊆ B) : (B : Set X) = (Set.univ : Set X) := by
  -- From density of `A` we have `closure A = univ`.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Since `A ⊆ B` and `B` is closed, `closure A ⊆ B`.
  have hClosureASubB : closure (A : Set X) ⊆ B := by
    have : closure (A : Set X) ⊆ closure (B : Set X) := closure_mono hSub
    simpa [hClosed.closure_eq] using this
  -- Hence `univ ⊆ B`.
  have hUnivSubB : (Set.univ : Set X) ⊆ B := by
    simpa [hClosureA] using hClosureASubB
  -- Combine the inclusions to obtain the equality.
  exact Set.Subset.antisymm (by
    intro x _
    simp) hUnivSubB

theorem Topology.isOpen_dense_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen A → Dense A → closure (interior A) = (Set.univ : Set X) := by
  intro hOpen hDense
  have hEq : closure (interior A) = closure A :=
    Topology.isOpen_closure_interior_eq_closure (A := A) hOpen
  simpa [hDense.closure_eq] using hEq

theorem Topology.interior_closure_union_subset_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∪ B) : Set X)) ⊆
      closure (A : Set X) ∪ closure (B : Set X) := by
  intro x hx
  -- From membership in the interior, obtain membership in the closure.
  have hx_cl : (x : X) ∈ closure ((A ∪ B) : Set X) := interior_subset hx
  -- Rewrite the closure of the union as the union of the closures.
  simpa [closure_union] using hx_cl

theorem Topology.interior_eq_self_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (A : Set X) → Topology.P2 A := by
  intro hIntEq
  -- From `interior A = A` we deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (isOpen_iff_interior_eq (A := A)).2 hIntEq
  -- Every open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (A := A) hOpen

theorem Topology.frontier_subset_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (A : Set X) → frontier (A : Set X) ⊆ A := by
  intro hClosed x hxFrontier
  -- From `hxFrontier` we obtain `x ∈ closure A`.
  have hx_closure : (x : X) ∈ closure (A : Set X) := hxFrontier.1
  -- Since `A` is closed, `closure A = A`.
  simpa [hClosed.closure_eq] using hx_closure

theorem Topology.frontier_eq_closure_inter_closure_compl {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  -- We prove the equality by mutual inclusion.
  apply Set.Subset.antisymm
  · -- `⊆` : every frontier point lies in both closures.
    intro x hx
    exact
      And.intro
        (Topology.frontier_subset_closure (A := A) hx)
        (Topology.frontier_subset_closure_compl (A := A) hx)
  · -- `⊇` : a point in the intersection of the closures lies in the frontier.
    rintro x ⟨hxClA, hxClAc⟩
    -- We first show that `x ∉ interior A`.
    have hNotInt : x ∉ interior (A : Set X) := by
      intro hxInt
      -- Because `x ∈ interior A`, the open set `interior A`
      -- is a neighbourhood of `x` contained in `A`.
      -- This contradicts `x ∈ closure Aᶜ`, which requires every neighbourhood
      -- of `x` to meet `Aᶜ`.
      have hNonempty :
          ((interior (A : Set X)) ∩ (Aᶜ : Set X)).Nonempty :=
        (mem_closure_iff.1 hxClAc) (interior (A : Set X)) isOpen_interior hxInt
      rcases hNonempty with ⟨y, hyInt, hyAc⟩
      have hInA : (y : X) ∈ (A : Set X) := interior_subset hyInt
      have hNotInA : (y : X) ∉ (A : Set X) := by
        simpa using hyAc
      exact hNotInA hInA
    -- Having `x ∈ closure A` and `x ∉ interior A`, we are in the frontier.
    exact And.intro hxClA hNotInt

theorem Topology.P3_iUnion_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P3 (s i)) →
      closure (interior (closure (⋃ i, s i : Set X))) = closure (⋃ i, s i : Set X) := by
  intro hP3
  have hP3Union : Topology.P3 (⋃ i, s i) :=
    Topology.P3_iUnion (s := s) hP3
  exact
    Topology.P3_implies_closure_interior_closure_eq_closure
      (A := ⋃ i, s i) hP3Union

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = s := by
  simpa using compl_compl (s := s)

theorem Topology.dense_right_implies_P3_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Dense (B : Set X) → Topology.P3 (A ∪ B) := by
  intro hDense
  intro x hxUnion
  -- `closure B = univ` because `B` is dense.
  have hClB : closure (B : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence `closure (A ∪ B)` is also the whole space.
  have hClUnion : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; simp
    · intro y _
      -- Since `closure B = univ`, any point lies in `closure B`.
      have hy : (y : X) ∈ closure (B : Set X) := by
        simpa [hClB]
      -- `B ⊆ A ∪ B`, and closure is monotone.
      have : (closure (B : Set X) : Set X) ⊆ closure (A ∪ B : Set X) := by
        have hSub : (B : Set X) ⊆ A ∪ B := by
          intro z hz; exact Or.inr hz
        exact closure_mono hSub
      exact this hy
  -- Since `closure (A ∪ B) = univ`, its interior is also `univ`.
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hClUnion, interior_univ] using this

theorem Topology.interior_diff_isClosed_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsClosed (B : Set X) → interior (A \ B : Set X) = interior A \ B := by
  intro hClosed
  -- The complement of a closed set is open.
  have hOpen : IsOpen ((B : Set X)ᶜ) := hClosed.isOpen_compl
  -- Apply the lemma for an intersection with an open (right) set to `A ∩ Bᶜ`.
  have h :=
    Topology.interior_inter_isOpen_right (A := A) (B := (Bᶜ)) hOpen
  -- Rewrite intersections with set difference.
  simpa [Set.diff_eq] using h

theorem Topology.frontier_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier ((Aᶜ) : Set X) = frontier (A : Set X) := by
  calc
    frontier ((Aᶜ) : Set X)
        = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
          simpa [Set.compl_compl, Set.inter_comm] using
            (Topology.frontier_eq_closure_inter_closure_compl
                (A := (Aᶜ : Set X)))
    _ = frontier (A : Set X) := by
          simpa using
            (Topology.frontier_eq_closure_inter_closure_compl
                (A := A)).symm

theorem Topology.P1_implies_closure_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure A ⊆ closure (interior (closure A)) := by
  intro hP1
  -- First, `P1 A` gives the inclusion `A ⊆ closure (interior (closure A))`.
  have hSub : (A : Set X) ⊆ closure (interior (closure A)) :=
    Topology.P1_implies_subset_closure_interior_closure (A := A) hP1
  -- Taking closures preserves inclusions.
  have hClSub :
      closure (A : Set X) ⊆ closure (closure (interior (closure A))) :=
    closure_mono hSub
  -- Simplify the right‐hand side using idempotence of `closure`.
  simpa [closure_closure] using hClSub

theorem Topology.closure_iInter_closure_eq_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Type*} (s : ι → Set X) :
    closure (⋂ i, closure (s i) : Set X) = ⋂ i, closure (s i) := by
  have hClosed : IsClosed (⋂ i, closure (s i) : Set X) :=
    isClosed_iInter (fun _ => isClosed_closure)
  simpa using hClosed.closure_eq



theorem Topology.P1_iff_frontier_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ frontier (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact
      Topology.P1_implies_frontier_subset_closure_interior (A := A) hP1
  · intro hFront
    exact
      Topology.P1_of_frontier_subset_closure_interior (A := A) hFront

theorem Topology.frontier_eq_univ_diff_interior_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A → frontier (A : Set X) = (Set.univ : Set X) \ interior A := by
  intro hDense
  have hCl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  simpa [frontier, hCl]

theorem Topology.isClosed_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (A : Set X) → IsClosed A := by
  intro hEq
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa [hEq] using hClosed



theorem Topology.isClosed_P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P2 A → Topology.P1 A := by
  intro hClosed hP2
  -- From the assumptions we first obtain that `A` is open.
  have hOpen : IsOpen A :=
    Topology.isClosed_P2_implies_isOpen (A := A) hClosed hP2
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (A := A) hOpen

theorem Topology.dense_left_implies_P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (A : Set X) → Topology.P3 (A ∪ B) := by
  intro hDense
  have h : Topology.P3 (B ∪ A) :=
    Topology.dense_right_implies_P3_union (A := B) (B := A) hDense
  simpa [Set.union_comm] using h

theorem Topology.frontier_def_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) = closure (A : Set X) \ interior (A : Set X) := by
  rfl

theorem Topology.dense_interior_implies_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 (closure (interior A)) := by
  intro hDense
  intro x hx
  -- Using density, the closure of `interior A` is the whole space.
  have hCl : closure (interior (A : Set X)) = (Set.univ : Set X) := hDense.closure_eq
  -- Rewrite the goal via this equality; everything reduces to `x ∈ univ`.
  have : x ∈ (Set.univ : Set X) := by
    simpa [hCl] using hx
  simpa [hCl, interior_univ, closure_closure] using this

theorem Topology.isOpen_diff_isClosed_right_implies_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsOpen A → IsClosed (B : Set X) → Topology.P1 (A \ B) := by
  intro hOpenA hClosedB
  -- `A \ B` is the intersection of two open sets: `A` and `Bᶜ`.
  have hOpenDiff : IsOpen (A \ B : Set X) := by
    have hOpenComplB : IsOpen ((Bᶜ) : Set X) := hClosedB.isOpen_compl
    simpa [Set.diff_eq] using hOpenA.inter hOpenComplB
  -- Any open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (A := A \ B) hOpenDiff

theorem Topology.frontier_closure_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (closure (A : Set X)) =
      closure (A : Set X) \ interior (closure (A : Set X)) := by
  -- By definition, `frontier S = closure S \ interior S`.  Applying this
  -- with `S = closure A` and simplifying the redundant `closure` yields
  -- the desired identity.
  simp [frontier, closure_closure]

theorem Topology.isOpen_diff_isClosed_right_implies_P2 {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsOpen A → IsClosed (B : Set X) → Topology.P2 (A \ B) := by
  intro hOpenA hClosedB
  -- `A \ B` is open since it is the intersection of the open set `A`
  -- with the open complement of the closed set `B`.
  have hOpenDiff : IsOpen (A \ B : Set X) := by
    have hOpenComplB : IsOpen ((Bᶜ) : Set X) := hClosedB.isOpen_compl
    simpa [Set.diff_eq] using hOpenA.inter hOpenComplB
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (A := A \ B) hOpenDiff

theorem Topology.P1_of_P1_and_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 A → (A ⊆ B) → (B ⊆ closure (A : Set X)) → Topology.P1 B := by
  intro hP1 hAB hBSub
  intro x hxB
  -- Step 1: move from `B` to `closure A`.
  have hx_clA : (x : X) ∈ closure (A : Set X) := hBSub hxB
  -- Step 2: use `P1 A` to pass to `closure (interior A)`.
  have h_clA_to_clIntA :
      (closure (A : Set X)) ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  have hx_clIntA : x ∈ closure (interior A) := h_clA_to_clIntA hx_clA
  -- Step 3: enlarge interiors via the inclusion `A ⊆ B`.
  have hIntMono : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusion.
  have hClMono :
      closure (interior A) ⊆ closure (interior B) :=
    closure_mono hIntMono
  -- Step 4: conclude the desired membership.
  exact hClMono hx_clIntA

theorem Topology.P1_implies_closure_frontier_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      closure (frontier (A : Set X)) ⊆ closure (interior A) := by
  intro hP1
  -- Step 1: `frontier A` is contained in `closure A`, and `closure A`
  -- is contained in `closure (interior A)` thanks to `P1`.
  have hFrontSub :
      (frontier (A : Set X) : Set X) ⊆ closure (interior A) := by
    have h₁ :
        (frontier (A : Set X) : Set X) ⊆ closure (A : Set X) :=
      Topology.frontier_subset_closure (A := A)
    have h₂ :
        closure (A : Set X) ⊆ closure (interior A) :=
      Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
    exact h₁.trans h₂
  -- Step 2: taking closures preserves inclusions; simplify the right‐hand side.
  have hCl :
      closure (frontier (A : Set X)) ⊆ closure (closure (interior A)) :=
    closure_mono hFrontSub
  simpa [closure_closure] using hCl

theorem Topology.interior_closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A \ B) : Set X)) ⊆ interior (closure (A : Set X)) := by
  -- Since `A \ B ⊆ A`, monotonicity gives all required inclusions.
  have hSub : ((A \ B) : Set X) ⊆ (A : Set X) := by
    intro x hx
    exact hx.1
  have hCl : closure ((A \ B) : Set X) ⊆ closure (A : Set X) :=
    closure_mono hSub
  exact interior_mono hCl

theorem Topology.P1_P2_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_implies_P1_P2_P3 (A := interior A) hOpen

theorem Topology.isOpen_P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A)) := by
  intro hOpen
  -- Equivalences available for open sets
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    (Topology.isOpen_P1_iff_P2 (A := A) hOpen)
  have hP2P3 : Topology.P2 A ↔ Topology.P3 A :=
    (Topology.isOpen_P2_iff_P3 (A := A) hOpen)
  constructor
  · intro hP2
    -- Deduce `P1` from `P2`
    have hP1 : Topology.P1 A := (hP1P2).mpr hP2
    -- Deduce `P3` from `P2`
    have hP3 : Topology.P3 A := (hP2P3).1 hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _hP3⟩
    -- Obtain `P2` from `P1`
    exact (hP1P2).1 hP1

theorem Topology.P1_implies_frontier_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      frontier (closure (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
  intro hP1
  -- `P1` also holds for `closure A`.
  have hP1_closure : Topology.P1 (closure (A : Set X)) :=
    Topology.P1_closure_of_P1 (A := A) hP1
  -- Apply the frontier lemma to `closure A`.
  have hIncl :
      frontier (closure (A : Set X)) ⊆
        closure (interior (closure (closure (A : Set X)))) :=
    Topology.P1_implies_frontier_subset_closure_interior_closure
      (A := closure (A : Set X)) hP1_closure
  -- Simplify the target using idempotence of `closure`.
  simpa [closure_closure] using hIncl

theorem Topology.interior_eq_self_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (A : Set X) → Topology.P3 A := by
  intro hIntEq
  have hOpen : IsOpen (A : Set X) :=
    (isOpen_iff_interior_eq (A := A)).2 hIntEq
  exact Topology.isOpen_implies_P3 (A := A) hOpen

theorem Topology.P3_of_frontier_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ interior (closure (A : Set X)) → Topology.P3 A := by
  intro hFront
  intro x hxA
  by_cases hxInt : x ∈ interior (A : Set X)
  ·
    -- Case 1: `x` already lies in `interior A`.
    have hSub :
        (interior (A : Set X) : Set X) ⊆ interior (closure (A : Set X)) := by
      have hIncl : (A : Set X) ⊆ closure (A : Set X) := subset_closure
      exact interior_mono hIncl
    exact hSub hxInt
  ·
    -- Case 2: `x` is not in `interior A`; hence it belongs to the frontier.
    have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
    have hxFront : x ∈ frontier (A : Set X) := And.intro hxCl hxInt
    exact hFront hxFront

theorem Topology.closure_diff_interior_compl_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) =
      closure (Aᶜ : Set X) \ interior (Aᶜ : Set X) := by
  calc
    closure (A : Set X) \ interior (A : Set X)
        = frontier (A : Set X) := rfl
    _ = frontier ((Aᶜ) : Set X) :=
      (Topology.frontier_compl (A := A)).symm
    _ = closure (Aᶜ : Set X) \ interior (Aᶜ : Set X) := rfl

theorem Topology.closure_diff_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A \ B) : Set X) ⊆ closure (A : Set X) := by
  -- Since `A \ B ⊆ A`, the monotonicity of `closure` yields the desired inclusion.
  have hSub : ((A \ B) : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact closure_mono hSub

theorem Topology.interior_subset_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (interior (A : Set X)) ⊆ interior (A ∪ B) := by
  intro x hx
  -- Since `A ⊆ A ∪ B`, monotonicity of `interior` yields the claim.
  have hSub : (A : Set X) ⊆ A ∪ B := by
    intro y hy
    exact Or.inl hy
  exact (interior_mono hSub) hx

theorem Topology.interior_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP1
  exact Topology.interior_closure_subset_closure_interior_of_P1 (A := A) hP1

theorem Topology.frontier_eq_empty_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) → Topology.P1 A := by
  intro hFrontier
  have hSubset : frontier (A : Set X) ⊆ closure (interior A) := by
    simpa [hFrontier] using (Set.empty_subset _)
  exact
    Topology.P1_of_frontier_subset_closure_interior (A := A) hSubset

theorem Topology.P1_dense_implies_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → Dense A → closure (interior A) = (Set.univ : Set X) := by
  intro hP1 hDense
  -- `P1 A` gives `closure (interior A) = closure A`.
  have h₁ : closure (interior A) = closure A :=
    Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  -- Density of `A` yields `closure A = univ`.
  have h₂ : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Combine the two equalities.
  simpa [h₂] using h₁

theorem Topology.closure_inter_closed_eq_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (A : Set X) → IsClosed (B : Set X) →
      closure (A ∩ B : Set X) = (A ∩ B : Set X) := by
  intro hClosedA hClosedB
  have hClosed : IsClosed (A ∩ B : Set X) := hClosedA.inter hClosedB
  simpa using hClosed.closure_eq

theorem Topology.closure_interior_eq_self_iff_isClosed_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (A : Set X) ↔ (IsClosed A ∧ Topology.P1 A) := by
  constructor
  · intro hEq
    -- `A` is closed because it is the closure of some set.
    have hClosed : IsClosed (A : Set X) := by
      have : IsClosed (closure (interior A) : Set X) := isClosed_closure
      simpa [hEq] using this
    -- Use the closedness to rewrite `closure A`.
    have hClA : closure (A : Set X) = (A : Set X) := hClosed.closure_eq
    -- Turn the given equality into the characterisation of `P1`.
    have hP1 : Topology.P1 A := by
      -- Both closures coincide because they are equal to `A`.
      have hClosureEq : closure (interior A) = closure (A : Set X) := by
        simpa [hEq, hClA]
      exact
        (Topology.P1_iff_closure_interior_eq_closure (A := A)).mpr hClosureEq
    exact And.intro hClosed hP1
  · rintro ⟨hClosed, hP1⟩
    exact
      Topology.isClosed_P1_implies_closure_interior_eq_self
        (A := A) hClosed hP1

theorem Topology.dense_interior_implies_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) → closure (A : Set X) = (Set.univ : Set X) := by
  intro hDense
  -- `closure (interior A)` is the whole space because `interior A` is dense.
  have hInt : closure (interior (A : Set X)) = (Set.univ : Set X) := hDense.closure_eq
  -- Monotonicity of `closure` for the inclusion `interior A ⊆ A`.
  have hUnivSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    have hMono : (closure (interior (A : Set X)) : Set X) ⊆ closure (A : Set X) := by
      have hSub : (interior (A : Set X) : Set X) ⊆ A := interior_subset
      exact closure_mono hSub
    simpa [hInt] using hMono
  -- Combine with the trivial inclusion `closure A ⊆ univ`.
  apply Set.Subset.antisymm
  · intro x hx; simp
  · exact hUnivSub

theorem Topology.P2_union_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B →
      closure (interior (closure (A ∪ B))) = closure (A ∪ B) := by
  intro hP2A hP2B
  have hP3A : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2A
  have hP3B : Topology.P3 B := Topology.P2_implies_P3 (A := B) hP2B
  exact
    Topology.P3_union_implies_closure_interior_closure_eq_closure
      (A := A) (B := B) hP3A hP3B

theorem Topology.frontier_subset_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → frontier (A : Set X) ⊆ (Aᶜ : Set X) := by
  intro hOpen x hxFront
  -- Rewrite the frontier of an open set.
  have hEq := Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hOpen
  have hxDiff : x ∈ closure (A : Set X) \ (A : Set X) := by
    simpa [hEq] using hxFront
  -- Extract the fact `x ∉ A`, hence `x ∈ Aᶜ`.
  rcases hxDiff with ⟨_, hxNotA⟩
  simpa [Set.mem_compl] using hxNotA

theorem Topology.closure_eq_interior_closure_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) =
      interior (closure (A : Set X)) ∪ frontier (A : Set X) := by
  ext x
  constructor
  · intro hxCl
    by_cases hIntCl : x ∈ interior (closure (A : Set X))
    · exact Or.inl hIntCl
    ·
      -- `x` is not in `interior (closure A)`; we show it lies in the frontier.
      have hNotIntA : x ∉ interior (A : Set X) := by
        intro hIntA
        have : x ∈ interior (closure (A : Set X)) :=
          (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hIntA
        exact hIntCl this
      have hxFront : x ∈ frontier (A : Set X) :=
        And.intro hxCl hNotIntA
      exact Or.inr hxFront
  · intro h
    cases h with
    | inl hIntCl => exact interior_subset hIntCl
    | inr hFront => exact hFront.1

theorem Topology.closure_frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → closure (frontier (A : Set X)) ⊆ A := by
  intro hClosed
  -- We already have `closure (frontier A) ⊆ closure A`.
  have h : closure (frontier (A : Set X)) ⊆ closure (A : Set X) :=
    Topology.closure_frontier_subset_closure (A := A)
  -- Since `A` is closed, `closure A = A`; rewrite and conclude.
  simpa [hClosed.closure_eq] using h

theorem Topology.closure_frontier_subset_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier (A : Set X)) ⊆
      closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  intro x hx
  -- `frontier A ⊆ closure A`
  have h₁ :
      (frontier (A : Set X) : Set X) ⊆ closure (A : Set X) :=
    Topology.frontier_subset_closure (A := A)
  -- Taking closures preserves inclusions.
  have h₁' :
      closure (frontier (A : Set X)) ⊆ closure (closure (A : Set X)) :=
    closure_mono h₁
  -- Simplify the right‐hand side.
  have hx₁ : x ∈ closure (A : Set X) := by
    have : x ∈ closure (closure (A : Set X)) := h₁' hx
    simpa [closure_closure] using this
  -- `frontier A ⊆ closure Aᶜ`
  have h₂ :
      (frontier (A : Set X) : Set X) ⊆ closure (Aᶜ : Set X) :=
    Topology.frontier_subset_closure_compl (A := A)
  -- Again, take closures.
  have h₂' :
      closure (frontier (A : Set X)) ⊆ closure (closure (Aᶜ : Set X)) :=
    closure_mono h₂
  have hx₂ : x ∈ closure (Aᶜ : Set X) := by
    have : x ∈ closure (closure (Aᶜ : Set X)) := h₂' hx
    simpa [closure_closure] using this
  exact And.intro hx₁ hx₂

theorem Topology.isClosed_P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A)) := by
  intro hClosed
  have h₁ := (Topology.isClosed_P2_iff_isOpen (A := A) hClosed)
  have h₂ := (Topology.isClosed_isOpen_iff_P1_and_P3 (A := A) hClosed)
  simpa using h₁.trans h₂

theorem Topology.closure_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∪ closure (Aᶜ : Set X) = (Set.univ : Set X) := by
  -- We prove both inclusions separately.
  apply Set.Subset.antisymm
  · intro _; simp
  · intro x _
    by_cases h : x ∈ (A : Set X)
    ·
      have hx : x ∈ closure (A : Set X) := subset_closure h
      exact Or.inl hx
    ·
      have hxComp : x ∈ (Aᶜ : Set X) := h
      have hx : x ∈ closure (Aᶜ : Set X) := subset_closure hxComp
      exact Or.inr hx

theorem Topology.closure_frontier_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier (A : Set X)) =
      closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  calc
    closure (frontier (A : Set X))
        = frontier (A : Set X) := by
          simpa using
            (Topology.closure_frontier_eq_frontier (A := A))
    _ = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
          simpa using
            (Topology.frontier_eq_closure_inter_closure_compl (A := A))

theorem Topology.P2_of_frontier_subset_closure_interior_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (interior A) →
    Topology.P3 A → Topology.P2 A := by
  intro hFront hP3
  -- Obtain `P1 A` from the frontier hypothesis.
  have hP1 : Topology.P1 A :=
    Topology.P1_of_frontier_subset_closure_interior (A := A) hFront
  -- Combine `P1 A` and `P3 A` to deduce `P2 A`.
  exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3

theorem Topology.frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    frontier (A : Set X) ⊆ closure (B : Set X) := by
  intro x hxFront
  -- `x` lies in the closure of `A` by definition of the frontier.
  have hxClA : (x : X) ∈ closure (A : Set X) :=
    (Topology.frontier_subset_closure (A := A)) hxFront
  -- Monotonicity of `closure` for the inclusion `A ⊆ B`.
  have hClSub : (closure (A : Set X)) ⊆ closure (B : Set X) :=
    closure_mono hAB
  exact hClSub hxClA

theorem Topology.P2_implies_closure_frontier_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (frontier (A : Set X)) ⊆ closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact
    Topology.P1_implies_closure_frontier_subset_closure_interior
      (A := A) hP1

theorem Topology.frontier_eq_compl_of_open_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen A → Dense A → frontier (A : Set X) = (Aᶜ : Set X) := by
  intro hOpen hDense
  have h := Topology.frontier_eq_univ_diff_interior_of_dense (A := A) hDense
  simpa [hOpen.interior_eq, Set.compl_eq_univ_diff] using h

theorem Topology.isOpen_union_implies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen A → IsOpen B →
      (Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B)) := by
  intro hOpenA hOpenB
  have hOpenUnion : IsOpen (A ∪ B : Set X) := hOpenA.union hOpenB
  exact Topology.isOpen_implies_P1_P2_P3 (A := A ∪ B) hOpenUnion

theorem Topology.closure_frontier_frontier_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (frontier (frontier (A : Set X))) ⊆ closure (A : Set X) := by
  -- `frontier (frontier A)` is contained in `closure (frontier A)`.
  have h₁ :
      (frontier (frontier (A : Set X)) : Set X) ⊆
        closure (frontier (A : Set X)) :=
    Topology.frontier_subset_closure (A := frontier (A : Set X))
  -- `closure (frontier A)` is contained in `closure A`.
  have h₂ :
      (closure (frontier (A : Set X)) : Set X) ⊆
        closure (A : Set X) :=
    Topology.closure_frontier_subset_closure (A := A)
  -- Compose the inclusions and take closures.
  have h₃ :
      (frontier (frontier (A : Set X)) : Set X) ⊆
        closure (A : Set X) :=
    h₁.trans h₂
  simpa [closure_closure] using closure_mono h₃

theorem Topology.dense_interior_implies_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hDense
  have hEq : closure (A : Set X) = (Set.univ : Set X) :=
    Topology.dense_interior_implies_closure_eq_univ (A := A) hDense
  simpa [hEq] using (isOpen_univ : IsOpen (Set.univ : Set X))

theorem Topology.P3_implies_closure_frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      closure (frontier (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
  intro hP3
  -- From `P3`, the frontier of `A` is already contained in
  -- `closure (interior (closure A))`.
  have hSub :
      (frontier (A : Set X) : Set X) ⊆
        closure (interior (closure (A : Set X))) :=
    Topology.P3_implies_frontier_subset_closure_interior_closure
      (A := A) hP3
  -- Taking closures preserves inclusions; simplify the right‐hand side.
  simpa [closure_closure] using closure_mono hSub

theorem Topology.frontier_closure_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (closure (A : Set X)) ⊆ frontier (A : Set X) := by
  intro x hx
  rcases hx with ⟨hx_closure_cl, hx_not_int_cl⟩
  -- `x` is in `closure A`
  have hx_closure : (x : X) ∈ closure (A : Set X) := by
    simpa [closure_closure] using hx_closure_cl
  -- If `x` were in `interior A`, it would lie in `interior (closure A)`,
  -- contradicting `hx_not_int_cl`.
  have hx_not_intA : x ∉ interior (A : Set X) := by
    intro hx_intA
    have hIntMono :
        (interior (A : Set X) : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    have : x ∈ interior (closure (A : Set X)) := hIntMono hx_intA
    exact hx_not_int_cl this
  exact And.intro hx_closure hx_not_intA

theorem Topology.frontier_eq_self_of_isClosed_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → interior (A : Set X) = (∅ : Set X) →
      frontier (A : Set X) = A := by
  intro hClosed hIntEmpty
  have h :=
    Topology.frontier_eq_self_diff_interior_of_isClosed (A := A) hClosed
  simpa [hIntEmpty, Set.diff_empty] using h

theorem Topology.dense_implies_frontier_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → frontier (interior (closure (A : Set X))) = (∅ : Set X) := by
  intro hDense
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simp [hDense.closure_eq, interior_univ]
  simpa [hInt, frontier_univ]

theorem Topology.closure_eq_self_union_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) = (A : Set X) ∪ frontier (A : Set X) := by
  ext x
  constructor
  · intro hxCl
    by_cases hxA : x ∈ (A : Set X)
    · exact Or.inl hxA
    ·
      -- Since `x ∉ A` and `x ∈ closure A`, we have `x ∈ frontier A`.
      have hxFront : x ∈ frontier (A : Set X) := by
        have hxNotInt : x ∉ interior (A : Set X) := by
          intro hxInt
          exact hxA (interior_subset hxInt)
        exact And.intro hxCl hxNotInt
      exact Or.inr hxFront
  · intro h
    cases h with
    | inl hxA =>
        exact subset_closure hxA
    | inr hxFront =>
        exact hxFront.1

theorem Topology.interior_inter_closures_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- `closure A ∩ closure B` is contained in each of `closure A` and `closure B`.
  have hSubA :
      (closure (A : Set X) ∩ closure (B : Set X) : Set X) ⊆ closure (A : Set X) :=
    by
      intro y hy
      exact hy.1
  have hSubB :
      (closure (A : Set X) ∩ closure (B : Set X) : Set X) ⊆ closure (B : Set X) :=
    by
      intro y hy
      exact hy.2
  -- Apply monotonicity of `interior` to both inclusions.
  have hIntA :
      interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
        interior (closure (A : Set X)) :=
    interior_mono hSubA
  have hIntB :
      interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
        interior (closure (B : Set X)) :=
    interior_mono hSubB
  exact And.intro (hIntA hx) (hIntB hx)

theorem Topology.P3_implies_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      (A : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) := by
  intro hP3 x hxA
  -- Step 1: from `P3` obtain that `x` is in `interior (closure A)`.
  have hx_int_cl : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Step 2: establish the inclusion
  --   `interior (closure A) ⊆ interior (closure (interior (closure A)))`.
  have hIncl :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) := by
    -- `P3` gives `closure A ⊆ closure (interior (closure A))`.
    have hClSub :
        (closure (A : Set X)) ⊆
          closure (interior (closure (A : Set X))) :=
      Topology.P3_implies_closure_subset_closure_interior_closure
        (A := A) hP3
    -- Apply monotonicity of `interior` to the inclusion of closures.
    exact interior_mono hClSub
  -- Step 3: combine the facts to obtain the desired membership.
  exact hIncl hx_int_cl

theorem Topology.closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∩ interior (Aᶜ : Set X) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · -- Show that the intersection is contained in `∅`.
    intro x hx
    rcases hx with ⟨hxCl, hxInt⟩
    -- Use the neighbourhood formulation of `closure`.
    have h :=
      (mem_closure_iff.1 hxCl) (interior (Aᶜ : Set X)) isOpen_interior hxInt
    rcases h with ⟨y, hyInt, hyA⟩
    -- `y` is simultaneously in `A` and `Aᶜ`, contradiction.
    have hyNotA : (y : X) ∉ (A : Set X) := by
      have : (y : X) ∈ (Aᶜ : Set X) := interior_subset hyInt
      simpa [Set.mem_compl] using this
    exact (hyNotA hyA).elim
  · -- The empty set is contained in every set.
    exact Set.empty_subset _

theorem Topology.compl_frontier_eq_union_interiors {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (frontier (A : Set X))ᶜ = interior (A : Set X) ∪ interior (Aᶜ : Set X) := by
  calc
    (frontier (A : Set X))ᶜ
        = (closure (A : Set X) ∩ closure (Aᶜ : Set X))ᶜ := by
          simpa [Topology.frontier_eq_closure_inter_closure_compl (A := A)]
    _ = (closure (A : Set X))ᶜ ∪ (closure (Aᶜ : Set X))ᶜ := by
          -- De Morgan’s law for complements
          simp [Set.compl_inter]
    _ = interior (Aᶜ : Set X) ∪ interior (A : Set X) := by
          -- `interior (sᶜ) = (closure s)ᶜ`
          simp [interior_compl]
    _ = interior (A : Set X) ∪ interior (Aᶜ : Set X) := by
          simpa [Set.union_comm]

theorem Topology.closure_eq_closure_interior_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = closure (interior A) ∪ frontier (A : Set X) := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    intro x hxClA
    -- Case distinction on whether `x` lies in `interior A`.
    by_cases hxIntA : x ∈ interior (A : Set X)
    · -- If `x ∈ interior A`, then `x ∈ closure (interior A)`.
      have hxClInt : (x : X) ∈ closure (interior A) :=
        subset_closure hxIntA
      exact Or.inl hxClInt
    · -- Otherwise `x ∉ interior A`; since `x ∈ closure A`, `x` is in the frontier.
      have hxFront : (x : X) ∈ frontier (A : Set X) :=
        And.intro hxClA hxIntA
      exact Or.inr hxFront
  · -- `⊇` direction
    intro x hxUnion
    cases hxUnion with
    | inl hxClInt =>
        -- `closure (interior A) ⊆ closure A`
        exact
          (Topology.closure_interior_subset_closure (A := A)) hxClInt
    | inr hxFront =>
        -- By definition of the frontier, `x ∈ closure A`.
        exact hxFront.1

theorem Topology.frontier_inter_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) ∩ interior (A : Set X) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hFront, hInt⟩
    exact (hFront.2 hInt).elim
  · intro hx
    cases hx

theorem Topology.closure_union_eq_univ_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (A : Set X) → closure (A ∪ B : Set X) = (Set.univ : Set X) := by
  intro hDense
  -- We prove the equality by mutual inclusion.
  apply Set.Subset.antisymm
  · -- `closure (A ∪ B) ⊆ univ` is trivial.
    intro _ _
    simp
  · -- For the reverse inclusion, start with an arbitrary point `x : X`.
    intro x _
    -- Density gives `x ∈ closure A = univ`.
    have hxClA : (x : X) ∈ closure (A : Set X) := by
      simpa [hDense.closure_eq] using (by
        have : x ∈ (Set.univ : Set X) := by simp
        simpa using this)
    -- Since `A ⊆ A ∪ B`, monotonicity of `closure` yields the goal.
    have hIncl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
      have hSub : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      exact closure_mono hSub
    exact hIncl hxClA

theorem Topology.frontier_inter_self_eq_empty_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen A → frontier (A : Set X) ∩ A = (∅ : Set X) := by
  intro hOpen
  simpa [hOpen.interior_eq] using
    (Topology.frontier_inter_interior_eq_empty (A := A))

theorem Topology.interior_eq_interior_closure_diff_frontier {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) =
      interior (closure (A : Set X)) \ frontier (A : Set X) := by
  ext x
  constructor
  · intro hxIntA
    -- `x` lies in the interior of `closure A` because `A ⊆ closure A`.
    have hxIntCl : x ∈ interior (closure (A : Set X)) := by
      have hSub : (A : Set X) ⊆ closure (A : Set X) := subset_closure
      exact (interior_mono hSub) hxIntA
    -- Points of `interior A` are never in the frontier of `A`.
    have hxNotFront : x ∉ frontier (A : Set X) := by
      intro hxFront
      exact hxFront.2 hxIntA
    exact And.intro hxIntCl hxNotFront
  · rintro ⟨hxIntCl, hxNotFront⟩
    -- We show that `x ∈ interior A`; otherwise we obtain a contradiction.
    by_contra hNotIntA
    -- `x` lies in `closure A` because it is in `interior (closure A)`.
    have hxClA : x ∈ closure (A : Set X) := interior_subset hxIntCl
    -- Hence `x` would be in the frontier of `A`, contradicting `hxNotFront`.
    have hxFront : x ∈ frontier (A : Set X) := And.intro hxClA hNotIntA
    exact hxNotFront hxFront

theorem Topology.interior_closure_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) \ interior (A : Set X) ⊆
      frontier (A : Set X) := by
  intro x hx
  rcases hx with ⟨hxIntCl, hxNotIntA⟩
  have hxCl : (x : X) ∈ closure (A : Set X) := interior_subset hxIntCl
  exact And.intro hxCl hxNotIntA

theorem Topology.interior_union_frontier_union_interior_compl_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ frontier (A : Set X) ∪ interior (Aᶜ : Set X) =
      (Set.univ : Set X) := by
  calc
    interior (A : Set X) ∪ frontier (A : Set X) ∪ interior (Aᶜ : Set X)
        = frontier (A : Set X) ∪ (interior (A : Set X) ∪ interior (Aᶜ : Set X)) := by
          -- Reassociate and commute unions so that `frontier A` comes first
          simp [Set.union_left_comm, Set.union_comm, Set.union_assoc]
    _ = frontier (A : Set X) ∪ (frontier (A : Set X))ᶜ := by
          -- Replace the union of interiors with the complement of the frontier
          simpa [Topology.compl_frontier_eq_union_interiors (A := A), Set.union_comm]
    _ = (Set.univ : Set X) := by
          -- A set union its complement is the whole space
          simpa using Set.union_compl_self (frontier (A : Set X))

theorem Topology.closure_interior_diff_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ (A : Set X) ⊆ frontier (A : Set X) := by
  intro x hx
  -- `hx` gives the facts that `x ∈ closure (interior A)` and `x ∉ A`.
  have hx_cl_int : x ∈ closure (interior A) := hx.1
  have hx_not_A  : x ∉ (A : Set X)     := hx.2
  -- Since `interior A ⊆ A ⊆ closure A`, we have
  -- `closure (interior A) ⊆ closure A`; hence `x ∈ closure A`.
  have hsubset : (closure (interior A) : Set X) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (A := A)
  have hx_cl_A : x ∈ closure (A : Set X) := hsubset hx_cl_int
  -- To be in the frontier of `A`, we also need `x ∉ interior A`.
  have hx_not_int : x ∉ interior (A : Set X) := by
    intro hx_int
    exact hx_not_A (interior_subset hx_int)
  -- Assemble the two conditions defining the frontier.
  exact And.intro hx_cl_A hx_not_int

theorem Topology.isOpen_of_interior_closure_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (A : Set X)) = A → IsOpen A := by
  intro hEq
  have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa [hEq] using this

theorem Topology.P1_closure_iff_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (A : Set X)) ↔
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- Use the existing equivalence with `S = closure A`.
  have hEquiv :=
    (Topology.P1_iff_closure_interior_eq_closure
        (A := closure (A : Set X)))
  constructor
  · intro hP1
    have h := (hEquiv).1 hP1
    simpa [closure_closure] using h
  · intro hEq
    -- Rewrite the given equality to the form expected by `hEquiv`.
    have h' :
        closure (interior (closure (A : Set X))) =
          closure (closure (A : Set X)) := by
      simpa [closure_closure] using hEq
    exact (hEquiv).2 h'

theorem Topology.closure_frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (frontier (A : Set X)) =
      closure (A : Set X) \ interior (A : Set X) := by
  -- The frontier of any set is closed, hence equal to its own closure.
  have hClosed : IsClosed (frontier (A : Set X)) := isClosed_frontier
  calc
    closure (frontier (A : Set X))
        = frontier (A : Set X) := by
          simpa using hClosed.closure_eq
    _ = closure (A : Set X) \ interior (A : Set X) := rfl

theorem Topology.closure_interior_union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X) ∪ frontier (A : Set X)) = closure (A : Set X) := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` : the left‐hand side is contained in `closure A`
    intro x hx
    -- First note that `interior A ⊆ A` and `frontier A ⊆ closure A`.
    have h₁ : (interior (A : Set X) ∪ frontier (A : Set X) : Set X) ⊆
        closure (A : Set X) := by
      intro y hy
      cases hy with
      | inl hyInt =>
          exact subset_closure (interior_subset hyInt)
      | inr hyFront =>
          exact (Topology.frontier_subset_closure (A := A)) hyFront
    -- Taking closures preserves inclusions; simplify with `closure_closure`.
    have : (closure (interior (A : Set X) ∪ frontier (A : Set X)) : Set X) ⊆
        closure (closure (A : Set X)) := closure_mono h₁
    simpa [closure_closure] using this hx
  · -- `⊇` : `closure A` is contained in the left‐hand side
    intro x hxClA
    -- It suffices to show `A ⊆ interior A ∪ frontier A`, because
    -- then monotonicity of `closure` yields the result.
    have hIncl : (A : Set X) ⊆ interior (A : Set X) ∪ frontier (A : Set X) := by
      intro y hyA
      by_cases hyInt : y ∈ interior (A : Set X)
      · exact Or.inl hyInt
      ·
        have hyFront : (y : X) ∈ frontier (A : Set X) :=
          And.intro (subset_closure hyA) hyInt
        exact Or.inr hyFront
    -- Apply monotonicity of `closure` to the inclusion `A ⊆ interior A ∪ frontier A`.
    have hClIncl :
        (closure (A : Set X) : Set X) ⊆
          closure (interior (A : Set X) ∪ frontier (A : Set X)) :=
      closure_mono hIncl
    exact hClIncl hxClA

