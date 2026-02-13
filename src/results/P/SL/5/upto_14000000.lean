

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P1, P2] at *
  intro x hx
  exact interior_subset (h hx)

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2, P3] at *
  intro x hxA
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact (interior_mono hsubset) (h hxA)

theorem interior_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  ext x
  constructor
  · intro hx
    have hsubset : closure (interior (closure A)) ⊆ closure A := by
      have h : (interior (closure A) : Set X) ⊆ closure A := interior_subset
      simpa using (closure_mono h)
    exact (interior_mono hsubset) hx
  · intro hx
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    have hsubset : interior (closure A) ⊆ closure (interior (closure A)) := subset_closure
    have hsub_interior : interior (closure A) ⊆ interior (closure (interior (closure A))) :=
      interior_maximal hsubset h_open
    exact hsub_interior hx

theorem closure_interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  ext x
  constructor
  · intro hx
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have hmem : x ∈ closure (closure (interior A)) :=
      (closure_mono hsubset) hx
    simpa [closure_closure] using hmem
  · intro hx
    have hsubset₁ : interior A ⊆ closure (interior A) := subset_closure
    have hopen : IsOpen (interior A) := isOpen_interior
    have hsubset₂ : interior A ⊆ interior (closure (interior A)) :=
      interior_maximal hsubset₁ hopen
    exact (closure_mono hsubset₂) hx

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    P2 A := by
  dsimp [P2]
  intro x hx
  -- `closure A` is a neighborhood of `x`
  have h_closure_nhds : closure A ∈ 𝓝 x := by
    have hA_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hx
    exact Filter.mem_of_superset hA_nhds (subset_closure : A ⊆ closure A)
  -- hence `x ∈ interior (closure A)`
  have h_mem : x ∈ interior (closure A) :=
    (mem_interior_iff_mem_nhds).mpr h_closure_nhds
  -- rewrite using `interior A = A` because `A` is open
  have h_intA : interior A = A := hA.interior_eq
  simpa [h_intA] using h_mem

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : P1 (X := X) A) (hB : P1 (X := X) B) : P1 (A ∪ B) := by
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ closure (interior A) := hA hxA
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (closure_mono hsubset) hxA'
  | inr hxB =>
      have hxB' : x ∈ closure (interior B) := hB hxB
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (closure_mono hsubset) hxB'

theorem isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    P3 (X := X) A := by
  dsimp [P3]
  intro x hxA
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
  exact hsubset hxA

theorem interior_closure_idempotent_iter {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using interior_closure_idempotent (X := X) (A := interior A)

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : P2 (X := X) A) (hB : P2 (X := X) B) :
    P2 (A ∪ B) := by
  dsimp [P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset_inner : (interior A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_inner
      exact (interior_mono hsubset) hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset_inner : (interior B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_inner
      exact (interior_mono hsubset) hxB'

theorem isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : P1 (X := X) A := by
  have hP2 : P2 (X := X) A := isOpen_implies_P2 (X := X) (A := A) hA
  exact P2_implies_P1 (X := X) (A := A) hP2

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : P3 (X := X) A) (hB : P3 (X := X) B) :
    P3 (A ∪ B) := by
  dsimp [P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hA hxA
      have hsubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (interior_mono hsubset) hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hB hxB
      have hsubset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (interior_mono hsubset) hxB'

theorem closure_interior_idempotent_iter {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using closure_interior_idempotent (X := X) (A := closure A)

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    P2 (X := X) (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior A) h_open

theorem P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    P3 (X := X) (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  exact isOpen_implies_P3 (X := X) (A := interior A) h_open

theorem P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    P1 (X := X) (interior A) := by
  have hP2 : P2 (X := X) (interior A) := P2_interior (X := X) A
  exact P2_implies_P1 (X := X) (A := interior A) hP2

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  exact interior_mono (Topology.closure_interior_mono hAB)

theorem closure_interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have hsubset : (A : Set X) ⊆ closure A := subset_closure
  exact Topology.closure_interior_mono hsubset

theorem interior_closure_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : (closure (A ∩ B) : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : (closure (A ∩ B) : Set X) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact ⟨(interior_mono hA) hx, (interior_mono hB) hx⟩

theorem interior_closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (interior_mono hsubset) hxA
  | inr hxB =>
      have hsubset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (interior_mono hsubset) hxB

theorem interior_closure_idempotent_three {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  have h1 := interior_closure_idempotent_iter (X := X) (A := closure A)
  have h2 := interior_closure_idempotent (X := X) (A := A)
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using h1
    _ = interior (closure A) := by
          simpa using h2

theorem closure_interior_idempotent_three {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
          simpa using closure_interior_idempotent_iter (X := X) (A := interior A)
    _ = closure (interior A) := by
          simpa using closure_interior_idempotent (X := X) (A := A)

theorem P2_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior (closure (interior A))) h_open

theorem closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  have h : (interior (closure A) : Set X) ⊆ closure A := interior_subset
  simpa using closure_mono h

theorem closure_interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hA : (interior (A ∩ B) : Set X) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : (interior (A ∩ B) : Set X) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact ⟨(closure_mono hA) hx, (closure_mono hB) hx⟩

theorem interior_closure_interior_subset_closure_interior_and_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior A) ∩ interior (closure A) := by
  intro x hx
  have h_closure : x ∈ closure (interior A) := interior_subset hx
  have hsub : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  have h_interior : x ∈ interior (closure A) := (interior_mono hsub) hx
  exact ⟨h_closure, h_interior⟩

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    P2 (X := X) (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior (closure A)) h_open

theorem P1_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    closure A ⊆ closure (interior A) := by
  -- From `P1`, we know `A ⊆ closure (interior A)`.
  have h : (A : Set X) ⊆ closure (interior A) := hA
  -- Taking closures on both sides yields the desired inclusion.
  have h' : closure A ⊆ closure (closure (interior A)) := closure_mono h
  simpa using h'

theorem closure_interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : (interior A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (closure_mono hsubset) hxA
  | inr hxB =>
      have hsubset : (interior B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (closure_mono hsubset) hxB

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    P1 (X := X) (interior (closure A)) := by
  have hP2 : P2 (X := X) (interior (closure A)) :=
    P2_interior_closure (X := X) A
  exact P2_implies_P1 (X := X) (A := interior (closure A)) hP2

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- Using idempotency of `closure ∘ interior`.
  have h_eq : closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using Topology.closure_interior_idempotent (X := X) (A := interior A)
  -- Rewrite the membership with the obtained equality.
  have : x ∈ closure (interior (closure (interior A))) := by
    have hx' : x ∈ closure (interior A) := hx
    simpa [h_eq] using hx'
  exact this

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    P3 (X := X) (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact isOpen_implies_P3 (X := X) (A := interior (closure A)) h_open

theorem interior_closure_idempotent_four {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  simp [Topology.interior_closure_idempotent]

theorem closure_interior_idempotent_four {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- The three-step idempotency.
  have h3 :=
    Topology.closure_interior_idempotent_three (X := X) (A := A)
  -- Apply `closure ∘ interior` once more to both sides.
  have h4 :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using (congrArg (fun S : Set X => closure (interior S)) h3)
  -- The basic idempotency.
  have h1 :=
    Topology.closure_interior_idempotent (X := X) (A := A)
  -- Assemble the equalities.
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
          simpa using h4
    _ = closure (interior A) := by
          simpa using h1

theorem interior_closure_idempotent_five {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (interior (closure A))))))))) =
      interior (closure A) := by
  simp [Topology.interior_closure_idempotent]

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  exact hsubset hx

theorem closure_eq_univ_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (A : Set X) = Set.univ) : P3 (X := X) A := by
  dsimp [P3]
  intro x hx
  -- acknowledge the assumption to avoid unused variable warnings
  have _ : x ∈ A := hx
  -- since `closure A = univ`, its interior is also `univ`
  have : x ∈ interior (closure (A : Set X)) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hA, interior_univ] using this
  exact this

theorem P2_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    closure A ⊆ closure (interior A) := by
  -- From `P2`, we have `A ⊆ interior (closure (interior A))`.
  have h_subset : (A : Set X) ⊆ interior (closure (interior A)) := hA
  -- Taking closures yields the desired inclusion, modulo re-writing with idempotency.
  simpa [Topology.closure_interior_idempotent (X := X) (A := A)]
    using (closure_mono h_subset)

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (interior A).Nonempty := by
  classical
  by_contra hInt
  -- If `interior A` were empty, its closure would also be empty.
  have hInt_empty : interior A = (∅ : Set X) := by
    simpa using (Set.not_nonempty_iff_eq_empty).1 hInt
  have hClIntEmpty : closure (interior A) = (∅ : Set X) := by
    simpa [hInt_empty] using closure_empty
  -- Pick any point of `A`.
  obtain ⟨x, hxA⟩ := hA
  -- `P1` says this point lies in the closure of `interior A`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- But that closure is empty: contradiction.
  have : x ∈ (∅ : Set X) := by
    simpa [hClIntEmpty] using hx_cl
  simpa using this

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) = closure (interior A) := by
  constructor
  · intro hP1
    -- From `P1` we already have one inclusion of the closures.
    have h₁ : closure (A : Set X) ⊆ closure (interior A) :=
      Topology.P1_closure_subset (X := X) (A := A) hP1
    -- The reverse inclusion is always true.
    have h₂ : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- Hence the closures coincide.
    exact le_antisymm h₁ h₂
  · intro hEq
    -- To obtain `P1`, we show `A ⊆ closure (interior A)`.
    dsimp [Topology.P1]
    intro x hxA
    -- Every point of `A` lies in `closure A`, which equals the desired set.
    have : x ∈ closure (A : Set X) := subset_closure hxA
    simpa [hEq] using this

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure A := by
  have h : (interior A : Set X) ⊆ A := interior_subset
  exact closure_mono h

theorem interior_closure_eq_univ_of_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : closure (A : Set X) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = Set.univ := by
  simpa [hA, interior_univ]

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ⊆ interior (closure A) := by
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.P2 (X := X) A) :
    closure (A : Set X) = closure (interior A) := by
  have h₁ : closure (A : Set X) ⊆ closure (interior A) :=
    Topology.P2_closure_subset (X := X) (A := A) hA
  have h₂ : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (X := X) A
  exact le_antisymm h₁ h₂

theorem interior_eq_empty_of_interior_closure_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure (A : Set X)) = (∅ : Set X)) :
    interior (A : Set X) = (∅ : Set X) := by
  have hsub : interior (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    have hx' : x ∈ interior (closure (A : Set X)) :=
      (interior_subset_interior_closure (X := X) (A := A)) hx
    simpa [h] using hx'
  exact le_antisymm hsub (Set.empty_subset _)

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- First, note that `closure (interior A)` is contained in `closure A`,
  -- because `interior A ⊆ A` and `closure` is monotone.
  have hsubset : closure (interior A) ⊆ closure A := by
    exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Applying monotonicity of `interior` to the previous inclusion
  -- yields the desired result.
  exact interior_mono hsubset

theorem interior_closure_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (X := X) (closure A) := by
  dsimp [Topology.P1]
  intro x hx
  -- Since `A` is open, it is contained in the interior of its closure.
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
  -- Taking closures preserves inclusions.
  have h_closure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono h_subset
  exact h_closure_subset hx

theorem closure_interior_closure_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    closure (interior (closure (A : Set X))) ⊆ A := by
  -- Since `A` is closed, its closure is itself.
  have h_closure_eq : closure (A : Set X) = A := hA.closure_eq
  -- First, `interior (closure A)` is contained in `closure A`, hence in `A`.
  have h_subset : (interior (closure (A : Set X)) : Set X) ⊆ A := by
    have h' : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    simpa [h_closure_eq] using h'
  -- Taking closures preserves inclusions; rewrite via `closure A = A`.
  simpa [h_closure_eq] using closure_mono h_subset

theorem interior_closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP2 hxA⟩

theorem interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    interior (closure (A : Set X)) = interior (closure (interior A)) := by
  have h := Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hA
  simpa using congrArg interior h

theorem P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  dsimp [Topology.P1] at *
  intro x hx
  -- Step 1: From `P1_closure_subset`, points of `closure A` lie in `closure (interior A)`.
  have h₁ : x ∈ closure (interior A) := by
    have hsubset : closure (A : Set X) ⊆ closure (interior A) :=
      Topology.P1_closure_subset (X := X) (A := A) hA
    exact hsubset hx
  -- Step 2: `closure (interior A)` is contained in `closure (interior (closure A))`.
  have hsubset₂ : closure (interior A) ⊆
      closure (interior (closure (A : Set X))) :=
    Topology.closure_interior_subset_closure_interior_closure (X := X) A
  -- Combine the two inclusions.
  exact hsubset₂ h₁

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  constructor
  · intro _hP1
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hA
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2

theorem P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔ IsOpen A := by
  constructor
  · intro hP3
    -- Since `A` is closed, its closure is itself.
    have h_closure_eq : closure (A : Set X) = A := hA_closed.closure_eq
    -- `P3` provides `A ⊆ interior (closure A) = interior A`.
    have h_subset : (A : Set X) ⊆ interior A := by
      intro x hx
      have hx' : x ∈ interior (closure (A : Set X)) := hP3 hx
      simpa [h_closure_eq] using hx'
    -- Combine with `interior_subset` to get the equality `interior A = A`.
    have h_eq : interior (A : Set X) = A := by
      apply le_antisymm
      · exact interior_subset
      · exact h_subset
    -- Use the fact that `interior A` is open and rewrite with the equality.
    have : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [h_eq] using this
  · intro hOpen
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem closure_interior_idempotent_five {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  simp [Topology.closure_interior_idempotent]

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩

theorem interior_closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    interior (closure (A : Set X)) = interior (closure (interior A)) := by
  -- From `P1`, we know the closures coincide.
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hA
  -- Taking `interior` of both sides yields the desired equality.
  simpa using congrArg interior hEq

theorem closure_interior_subset_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- `interior A` is obviously contained in `A`.
  have h_subset : (interior (A : Set X) : Set X) ⊆ A := interior_subset
  -- Taking closures preserves inclusions.
  have h_closure_subset : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono h_subset
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using h_closure_subset

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  -- From `P2` we obtain `P3`.
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Apply the corresponding result for `P3`.
  exact
    Topology.interior_closure_nonempty_of_P3 (X := X) (A := A) hP3 hA

theorem P2_implies_P1_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : P2 (X := X) A) :
    P1 (X := X) (closure (A : Set X)) := by
  dsimp [P1] at *
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)` via `P2`.
  have h₁ : closure (A : Set X) ⊆ closure (interior A) :=
    P2_closure_subset (X := X) (A := A) hA
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure (A : Set X))) :=
    closure_interior_subset_closure_interior_closure (X := X) A
  -- Combine the two inclusions.
  have hx' : x ∈ closure (interior A) := h₁ hx
  exact h₂ hx'

theorem isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X := X) A) :
    IsOpen A := by
  -- From `P2` we obtain `P3`.
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Use the equivalence between `P3` and openness when `A` is closed.
  exact (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3

theorem closure_interior_eq_self_of_closed_and_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X := X) A) :
    closure (interior A) = A := by
  -- We obtain both inclusions separately and then use `le_antisymm`.
  apply le_antisymm
  · -- `closure (interior A)` is contained in `A` because `A` is closed.
    exact
      Topology.closure_interior_subset_of_closed (X := X) (A := A) hClosed
  · -- The converse inclusion follows from `P2`.
    intro x hxA
    -- `P2` yields that `x` belongs to the interior of `closure (interior A)`.
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
    -- Hence `x` lies in `closure (interior A)`.
    exact interior_subset hx_int

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x _hxA
  -- First, compute `interior (closure (interior A))`.
  have hint :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) := by
      simpa [h] using closure_univ
    simpa [h_closure, interior_univ]
  -- The desired membership is now immediate.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hint] using this

theorem P3_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : P3 (X := X) A) :
    closure (A : Set X) ⊆ closure (interior (closure A)) := by
  -- From `P3`, we have `A ⊆ interior (closure A)`.
  have hsubset : (A : Set X) ⊆ interior (closure A) := hA
  -- Taking closures preserves inclusions.
  exact closure_mono hsubset

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P1 (X := X) A := by
  -- First, `A` satisfies `P2` because its interior is dense.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h
  -- Since `P2` implies `P1`, we obtain the desired result.
  exact Topology.P2_implies_P1 (X := X) (A := A) hP2

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior A).Nonempty := by
  classical
  by_contra hInt
  -- `interior A` is empty by assumption.
  have hInt_empty : interior (A : Set X) = (∅ : Set X) := by
    simpa using (Set.not_nonempty_iff_eq_empty).1 hInt
  -- Hence `interior (closure (interior A))` is also empty.
  have hInt_closure_empty :
      interior (closure (interior (A : Set X))) = (∅ : Set X) := by
    simp [hInt_empty]
  -- Pick a point of `A`.
  rcases hA with ⟨x, hxA⟩
  -- `P2` says this point lies in `interior (closure (interior A))`,
  -- which we have just shown to be empty: contradiction.
  have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  have : x ∈ (∅ : Set X) := by
    simpa [hInt_closure_empty] using hx
  exact this

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  exact closure_mono (interior_mono (closure_mono hAB))

theorem closure_eq_closure_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.P3 (X := X) A) :
    closure (A : Set X) = closure (interior (closure A)) := by
  apply le_antisymm
  ·
    exact Topology.P3_closure_subset (X := X) (A := A) hA
  ·
    have hsubset : interior (closure (A : Set X)) ⊆ closure A := interior_subset
    have hclosure_subset :
        closure (interior (closure (A : Set X))) ⊆ closure (closure A) :=
      closure_mono hsubset
    simpa [closure_closure] using hclosure_subset

theorem interior_closure_nonempty_of_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (interior (A : Set X)).Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  rcases h with ⟨x, hx⟩
  have hx' : x ∈ interior (closure (A : Set X)) :=
    (interior_subset_interior_closure (X := X) (A := A)) hx
  exact ⟨x, hx'⟩

theorem closure_interior_eq_self_of_closed_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = A := by
  apply le_antisymm
  ·
    have hsubset : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (X := X) A
    simpa [hClosed.closure_eq] using hsubset
  ·
    exact hP1

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  -- First, `P1` together with the non-emptiness of `A` gives
  -- a non-empty interior of `A`.
  have hInt : (interior (A : Set X)).Nonempty :=
    Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA
  -- A non-empty interior of `A` implies a non-empty interior of its closure.
  exact
    Topology.interior_closure_nonempty_of_interior_nonempty
      (X := X) (A := A) hInt

theorem closure_interior_eq_self_of_closed_and_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    closure (interior A) = A := by
  -- Use the equality given by `P3` and rewrite with closedness of `A`.
  have h :=
    Topology.closure_eq_closure_interior_closure_of_P3 (X := X) (A := A) hP3
  have h' : (A : Set X) = closure (interior A) := by
    simpa [hClosed.closure_eq] using h
  simpa using h'.symm

theorem P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  constructor
  · intro hP2
    dsimp [Topology.P3] at *
    intro x hxA
    have hx_int_cl : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    have h_subset_cl : closure (interior (A : Set X)) ⊆ A := by
      have h_sub : (interior (A : Set X)) ⊆ A := interior_subset
      have h_cl : closure (interior (A : Set X)) ⊆ closure A := closure_mono h_sub
      simpa [hA_closed.closure_eq] using h_cl
    have h_subset_int :
        interior (closure (interior (A : Set X))) ⊆ interior A :=
      interior_mono h_subset_cl
    have hx_intA : x ∈ interior A := h_subset_int hx_int_cl
    simpa [hA_closed.closure_eq] using hx_intA
  · intro hP3
    dsimp [Topology.P2] at *
    intro x hxA
    have hx_int_clA : x ∈ interior (closure (A : Set X)) := hP3 hxA
    have hx_intA : x ∈ interior A := by
      simpa [hA_closed.closure_eq] using hx_int_clA
    have h_subset :
        interior (A : Set X) ⊆ interior (closure (interior (A : Set X))) := by
      have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
      have h_sub : interior (A : Set X) ⊆ closure (interior (A : Set X)) :=
        subset_closure
      exact interior_maximal h_sub h_open
    exact h_subset hx_intA

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) := by
  have h_open : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using Topology.isOpen_implies_P1 (X := X) (A := Set.univ) h_open

theorem P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ IsOpen A := by
  calc
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A :=
      Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hA_closed
    _ ↔ IsOpen A :=
      Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed

theorem interior_closure_eq_univ_iff_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (A : Set X)) = Set.univ ↔ closure (A : Set X) = Set.univ := by
  constructor
  · intro hInt
    -- `univ ⊆ closure A`
    have h_univ_sub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      intro x hx
      have hxInt : x ∈ interior (closure (A : Set X)) := by
        simpa [hInt] using hx
      exact interior_subset hxInt
    -- `closure A ⊆ univ` is trivial
    have h_closure_sub : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x hx
      trivial
    exact le_antisymm h_closure_sub h_univ_sub
  · intro hCl
    exact
      Topology.interior_closure_eq_univ_of_closure_eq_univ
        (X := X) (A := A) hCl

theorem P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  constructor
  · intro _hP1
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hA
  · intro _hP3
    exact Topology.isOpen_implies_P1 (X := X) (A := A) hA

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P3 (X := X) A := by
  -- First, dense interior implies `P2`.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h
  -- Since `P2` implies `P3`, we obtain the desired result.
  exact Topology.P2_implies_P3 (X := X) (A := A) hP2

theorem P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  have hInt : interior (A : Set X) = A := hA.interior_eq
  constructor
  · intro hP2
    dsimp [Topology.P3]
    intro x hxA
    have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    simpa [hInt] using hx
  · intro hP3
    dsimp [Topology.P2]
    intro x hxA
    have hx : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hInt] using hx

theorem P3_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    P3 (X := X) (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact isOpen_implies_P3 (X := X) (A := interior (closure (interior A))) h_open

theorem P1_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact
    Topology.isOpen_implies_P1
      (X := X)
      (A := interior (closure (interior A)))
      h_open

theorem interior_closure_interior_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    interior (closure (interior (A : Set X))) = interior A := by
  apply le_antisymm
  · -- `interior (closure (interior A)) ⊆ interior A`
    -- Since `interior A ⊆ A` and `A` is closed, the closure of `interior A`
    -- is contained in `A`.
    have hsubset : closure (interior (A : Set X)) ⊆ A := by
      have h₁ : (interior (A : Set X) : Set X) ⊆ A := interior_subset
      have h₂ : closure (interior (A : Set X)) ⊆ closure A := closure_mono h₁
      simpa [hA_closed.closure_eq] using h₂
    -- Applying monotonicity of `interior` yields the desired inclusion.
    exact interior_mono hsubset
  · -- `interior A ⊆ interior (closure (interior A))`
    -- `interior A` is open and contained in `closure (interior A)`.
    have hsubset : (interior (A : Set X) : Set X) ⊆ closure (interior (A : Set X)) :=
      subset_closure
    have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
    -- Use the maximality property of `interior`.
    exact interior_maximal hsubset h_open

theorem P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (closure (interior (closure A))) := by
  simpa using
    (Topology.P1_closure_interior (X := X) (A := closure A))

theorem P2_interior_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact
    Topology.isOpen_implies_P2
      (X := X)
      (A := interior (closure (interior (closure A))))
      h_open

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (Set.univ : Set X) := by
  have h_open : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using Topology.isOpen_implies_P2 (X := X) (A := Set.univ) h_open

theorem P1_iff_closure_interior_eq_self_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (X := X) A ↔ closure (interior A) = A := by
  -- Rewrite `closure A` using the closedness of `A`.
  have h_closure_eq : closure (A : Set X) = A := hA_closed.closure_eq
  -- Use the existing characterization of `P1`.
  have h :=
    Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  -- Substitute `closure A = A` in the equivalence and adjust the equality orientation.
  simpa [h_closure_eq, eq_comm] using h

theorem P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (closure (A : Set X))) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- Every point of `A` lies in `closure A`.
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
  -- Apply the `P2` hypothesis for `closure A`.
  have hx_int :
      x ∈ interior (closure (interior (closure (A : Set X)))) :=
    h hx_closure
  -- Use monotonicity of `interior` to pass to `interior (closure A)`.
  have h_subset :
      interior (closure (interior (closure (A : Set X))))
        ⊆ interior (closure (A : Set X)) := by
    have h_closure :
        closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
      Topology.closure_interior_closure_subset_closure (X := X) (A := A)
    exact interior_mono h_closure
  exact h_subset hx_int

theorem closure_interior_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    closure (interior A) = closure (interior (closure A)) := by
  apply le_antisymm
  ·
    exact
      Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A)
  ·
    intro x hx
    -- First, `x` lies in `closure A`.
    have hx_closureA :
        x ∈ closure (A : Set X) := by
      have hsubset :
          closure (interior (closure (A : Set X))) ⊆ closure A :=
        Topology.closure_interior_closure_subset_closure (X := X) (A := A)
      exact hsubset hx
    -- Use the equality `closure A = closure (interior A)` that follows from `P2`.
    have h_cl_eq :
        closure (A : Set X) = closure (interior A) :=
      Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hA
    simpa [h_cl_eq] using hx_closureA

theorem P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  dsimp [Topology.P1] at *
  intro x hx
  have hsubset :
      closure (A : Set X) ⊆ closure (interior (closure (A : Set X))) :=
    Topology.P3_closure_subset (X := X) (A := A) hA
  exact hsubset hx

theorem closure_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : (closure (A ∩ B : Set X)) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : (closure (A ∩ B : Set X)) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact ⟨hA hx, hB hx⟩

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x _
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [closure_univ, interior_univ] using this

theorem interior_closure_idempotent_six {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (interior (closure (interior (closure A))))))))))) =
      interior (closure A) := by
  simp [Topology.interior_closure_idempotent]

theorem interior_closure_eq_univ_implies_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure (A : Set X)) = Set.univ) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3] at *
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h] using this

theorem closure_interior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP1 hxA⟩

theorem interior_closure_inter_subset_interior_inter_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆ interior (closure A ∩ closure B) := by
  intro x hx
  have hsubset : closure (A ∩ B : Set X) ⊆ closure A ∩ closure B :=
    closure_inter_subset (X := X) (A := A) (B := B)
  exact (interior_mono hsubset) hx

theorem interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A :=
    (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hxB : x ∈ interior B :=
    (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hxA, hxB⟩

theorem closure_interior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure A := by
  simpa [hA.interior_eq]

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (X := X) (∅ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx

theorem closure_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = closure (A : Set X) := by
  simpa using
    ((Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1).symm

theorem interior_interiors_subset_interior_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∩ interior B ⊆ interior (A ∩ B) := by
  intro x hx
  -- `interior A ∩ interior B` is an open set …
  have h_open :
      IsOpen (interior (A : Set X) ∩ interior B) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).inter
      (isOpen_interior : IsOpen (interior B))
  -- … contained in `A ∩ B`.
  have h_subset :
      (interior (A : Set X) ∩ interior B : Set X) ⊆ A ∩ B := by
    intro y hy
    exact ⟨interior_subset hy.1, interior_subset hy.2⟩
  -- By maximality of the interior, it is contained in `interior (A ∩ B)`.
  have h_contained :
      (interior (A : Set X) ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
    interior_maximal h_subset h_open
  exact h_contained hx

theorem closure_inter_interior_subset_closure_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior (A ∩ B)) := by
  have hsubset :
      (interior (A : Set X) ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
    Topology.interior_interiors_subset_interior_inter (X := X) (A := A) (B := B)
  exact closure_mono hsubset

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (∅ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  cases hx

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P3 (X := X) A)
    (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) :
    Topology.P3 (X := X) (A ∪ B ∪ C) := by
  -- First, combine the properties for `A` and `B`.
  have hAB : Topology.P3 (X := X) (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Then, combine the result with `C`.
  have hABC : Topology.P3 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Re-associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABC

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P2 (X := X) A)
    (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) :
    Topology.P2 (X := X) (A ∪ B ∪ C) := by
  -- First, combine the properties for `A` and `B`.
  have hAB : Topology.P2 (X := X) (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Then, combine the result with `C`.
  have hABC : Topology.P2 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Re-associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABC

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P1 (X := X) A)
    (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) :
    Topology.P1 (X := X) (A ∪ B ∪ C) := by
  -- First, combine the properties for `A` and `B`.
  have hAB : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Then, combine the result with `C`.
  have hABC : Topology.P1 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P1_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Re-associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABC

theorem interior_closure_eq_interior_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior A := by
  simpa [hA_closed.closure_eq]

theorem P2_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : P2 (X := X) A) :
    P1 (X := X) A := by
  -- From the assumptions, `A` is both closed and satisfies `P2`. 
  -- The existing result `isOpen_of_isClosed_and_P2` tells us that `A` is open.
  have hOpen : IsOpen A :=
    isOpen_of_isClosed_and_P2 (X := X) (A := A) hClosed hP2
  -- Any open set satisfies `P1` by `isOpen_implies_P1`.
  exact isOpen_implies_P1 (X := X) (A := A) hOpen

theorem P3_interior_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (X := X) (interior (closure (interior (closure A)))) := by
  -- The interior of any set is open.
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  -- Hence it satisfies `P3`.
  exact
    Topology.isOpen_implies_P3
      (X := X)
      (A := interior (closure (interior (closure A))))
      h_open

theorem interior_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Step 1: `x ∈ interior (closure A)`
      have hxA' : x ∈ interior (closure A) :=
        (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxA
      -- Step 2: `closure A ⊆ closure (A ∪ B)`
      have hsubset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Step 3: `interior (closure A) ⊆ interior (closure (A ∪ B))`
      have hsubset_int :
          interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset
      exact hsubset_int hxA'
  | inr hxB =>
      -- Symmetric argument for `B`
      have hxB' : x ∈ interior (closure B) :=
        (interior_mono (subset_closure : (B : Set X) ⊆ closure B)) hxB
      have hsubset : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have hsubset_int :
          interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset
      exact hsubset_int hxB'

theorem closure_inter_of_interiors_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  simpa using
    (closure_inter_subset
        (X := X)
        (A := interior (A : Set X))
        (B := interior B))

theorem interior_inter_closure_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((closure (A : Set X)) ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) :=
    (interior_mono
      (Set.inter_subset_left :
        ((closure (A : Set X)) ∩ closure B) ⊆ closure A)) hx
  have hxB : x ∈ interior (closure B) :=
    (interior_mono
      (Set.inter_subset_right :
        ((closure (A : Set X)) ∩ closure B) ⊆ closure B)) hx
  exact ⟨hxA, hxB⟩

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First, combine the properties for `A`, `B`, and `C`.
  have hABC : Topology.P3 (X := X) (A ∪ B ∪ C) :=
    Topology.P3_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Then, combine the result with `D`.
  have hABCD : Topology.P3 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P3_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Re-associate the unions to match the required shape.
  simpa [Set.union_assoc] using hABCD

theorem P2_of_closure_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = Set.univ) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x _hxA
  -- Since `closure (interior A) = univ`, its interior is also `univ`.
  have : x ∈ interior (closure (interior (A : Set X))) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [h, interior_univ] using this
  exact this

theorem nonempty_of_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (interior (closure (A : Set X))).Nonempty) :
    (A : Set X).Nonempty := by
  classical
  by_contra hA
  -- If `A` were empty, so would be `interior (closure A)`, contradicting `h`.
  have hAeq : (A : Set X) = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hA
  have hIntEq : interior (closure (A : Set X)) = (∅ : Set X) := by
    simpa [hAeq] using by
      simp
  have hNonemptyEmpty : (∅ : Set X).Nonempty := by
    simpa [hIntEq] using h
  rcases hNonemptyEmpty with ⟨x, hx⟩
  exact hx

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First, combine the properties for `A`, `B`, and `C`.
  have hABC : Topology.P2 (X := X) (A ∪ B ∪ C) :=
    Topology.P2_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Then, combine the result with `D`.
  have hABCD : Topology.P2 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P2_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Re-associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABCD

theorem closure_interior_inter_subset_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior (A : Set X) ∩ interior B) := by
  have h :
      (interior (A ∩ B : Set X)) ⊆ interior (A : Set X) ∩ interior B :=
    Topology.interior_inter_subset (X := X) (A := A) (B := B)
  exact closure_mono h

theorem interior_closure_inter_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior A ∩ interior B)) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  simpa using
    (Topology.interior_closure_inter_subset
        (X := X)
        (A := interior A)
        (B := interior B))

theorem interior_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using hOpen.interior_eq

theorem P1_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- Combine `A`, `B`, and `C` using the existing three‐set union theorem.
  have hABC : Topology.P1 (X := X) (A ∪ B ∪ C) :=
    Topology.P1_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Now unite the result with `D`.
  have hABCD : Topology.P1 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P1_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Reassociate unions to match the target expression.
  simpa [Set.union_assoc] using hABCD

theorem P1_iff_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.P1_closure_subset (X := X) (A := A) hP1
  · intro hcl
    dsimp [Topology.P1] at *
    intro x hxA
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    exact hcl hx_cl

theorem P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) : Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  -- Since `closure A` is open, its interior equals itself.
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  -- Every point of `A` lies in `closure A`.
  have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [hInt] using hxCl

theorem closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have hx_cl : x ∈ closure (interior A) := interior_subset hx_int
  exact ⟨x, hx_cl⟩

theorem interior_closure_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) ⊆ closure A := by
  simpa using (interior_subset : interior (closure A) ⊆ closure A)

theorem isClosed_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = A) : IsClosed (A : Set X) := by
  -- The set `closure (interior A)` is always closed.
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Rewrite using the given equality.
  simpa [h] using hClosed

theorem isOpen_implies_all_P123 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    P1 (X := X) A ∧ P2 (X := X) A ∧ P3 (X := X) A := by
  exact
    ⟨isOpen_implies_P1 (X := X) (A := A) hA,
     isOpen_implies_P2 (X := X) (A := A) hA,
     isOpen_implies_P3 (X := X) (A := A) hA⟩

theorem interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ closure A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxInt
    have hxA : x ∈ (A : Set X) := interior_subset hxInt
    have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
    exact ⟨hxInt, hxCl⟩

theorem interior_closure_interior_eq_univ_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (Set.univ : Set X) ↔
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  simpa using
    (Topology.interior_closure_eq_univ_iff_closure_eq_univ
      (X := X) (A := interior A))

theorem interior_closure_interior_eq_interior_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (closure (interior (A : Set X))) = interior (closure A) := by
  simpa [hA.interior_eq]

theorem interior_closure_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- Every set is contained in the closure of itself.
  exact (subset_closure : (interior (closure (A : Set X)) : Set X) ⊆
    closure (interior (closure (A : Set X)))) hx

theorem closure_interior_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior (A : Set X))) = closure (interior A) := by
  simpa [interior_interior]

theorem closure_inter_closure_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  have hsubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
    closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  exact hsubset hx.1

theorem nonempty_of_closure_interior_nonempty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (closure (interior (A : Set X))).Nonempty) : (A : Set X).Nonempty := by
  classical
  by_contra hA
  -- From `¬A.Nonempty`, deduce `A = ∅`.
  have hAempty : (A : Set X) = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hA
  -- Hence `interior A = ∅`.
  have hIntEmpty : interior (A : Set X) = (∅ : Set X) := by
    simpa [hAempty] using interior_empty
  -- Consequently, its closure is also empty.
  have hClEmpty : closure (interior (A : Set X)) = (∅ : Set X) := by
    simpa [hIntEmpty] using closure_empty
  -- This contradicts the assumed non-emptiness.
  have hNonemptyEmpty : (∅ : Set X).Nonempty := by
    simpa [hClEmpty] using h
  rcases hNonemptyEmpty with ⟨x, hx⟩
  cases hx

theorem interior_nonempty_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) (hA : A.Nonempty) :
    (interior (A : Set X)).Nonempty := by
  -- From closedness and `P3`, we know that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  -- For an open set, its interior is itself.
  have hInt_eq : interior (A : Set X) = A := hOpen.interior_eq
  -- The non‐emptiness of `A` now yields the non‐emptiness of its interior.
  simpa [hInt_eq] using hA

theorem closure_union_interior_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  simpa using closure_union (interior (A : Set X)) (interior B)

theorem closure_interior_inter_interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ interior (closure A) ⊆
      closure (interior (closure A)) := by
  intro x hx
  -- `x` lies in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hx.1
  -- And `closure (interior A)` is contained in `closure (interior (closure A))`.
  have hsubset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (X := X) A
  -- Combining the two facts yields the desired membership.
  exact hsubset hx_cl

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : P2 (X := X) A) :
    P1 (X := X) A ∧ P3 (X := X) A := by
  exact ⟨P2_implies_P1 (X := X) (A := A) hP2,
        P2_implies_P3 (X := X) (A := A) hP2⟩

theorem union_interior_closure_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hxInt =>
      exact (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hxInt
  | inr hxCl =>
      have hsubset : closure (interior A) ⊆ closure A :=
        Topology.closure_interior_subset_closure (X := X) A
      exact hsubset hxCl

theorem interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : (interior A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hA
  | inr hB =>
      have hsubset : (interior B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hB

theorem P3_union_five {X : Type*} [TopologicalSpace X] {A B C D E : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E) := by
  -- Combine the first four sets.
  have hABCD : Topology.P3 (X := X) (A ∪ B ∪ C ∪ D) :=
    Topology.P3_union_four (X := X) (A := A) (B := B) (C := C) (D := D)
      hA hB hC hD
  -- Unite the result with `E`.
  have hABCDE : Topology.P3 (X := X) ((A ∪ B ∪ C ∪ D) ∪ E) :=
    Topology.P3_union (X := X) (A := A ∪ B ∪ C ∪ D) (B := E) hABCD hE
  -- Reassociate unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDE

theorem P3_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔ interior (A : Set X) = A := by
  -- First, rewrite `P3` in terms of openness using the existing equivalence.
  have h₁ :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  -- Next, relate openness to the equality `interior A = A`.
  have h₂ : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  simpa using h₁.trans h₂

theorem P2_union_five {X : Type*} [TopologicalSpace X] {A B C D E : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E) := by
  -- First, combine `A`, `B`, `C`, and `D`.
  have hABCD : Topology.P2 (X := X) (A ∪ B ∪ C ∪ D) :=
    Topology.P2_union_four (X := X) (A := A) (B := B) (C := C) (D := D)
      hA hB hC hD
  -- Unite the result with `E`.
  have hABCDE : Topology.P2 (X := X) ((A ∪ B ∪ C ∪ D) ∪ E) :=
    Topology.P2_union (X := X) (A := A ∪ B ∪ C ∪ D) (B := E) hABCD hE
  -- Re-associate unions to match the required shape.
  simpa [Set.union_assoc] using hABCDE

theorem interior_union_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have hOpen : IsOpen ((A ∪ B : Set X)) := hA.union hB
  simpa using hOpen.interior_eq

theorem closure_union_interiors_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  -- It suffices to show the inclusion at the level of the sets,
  -- and then use `closure_mono`.
  apply closure_mono
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` lies in `interior A`, which is contained in `interior (A ∪ B)`.
      have hsubset : (interior (A : Set X) : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA
  | inr hxB =>
      -- Symmetric argument for the case `x ∈ interior B`.
      have hsubset : (interior (B : Set X) : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB

theorem interior_diff_interior_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior ((A : Set X) \ interior A) = (∅ : Set X) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    -- `U` is an open subset of `A`.
    have hU_sub_A : (U : Set X) ⊆ A := by
      intro y hy
      exact (hUsub hy).1
    -- By maximality of the interior, `U ⊆ interior A`.
    have hU_sub_intA : (U : Set X) ⊆ interior (A : Set X) :=
      interior_maximal hU_sub_A hUopen
    -- Hence `x ∈ interior A`.
    have hx_intA : x ∈ interior (A : Set X) := hU_sub_intA hxU
    -- But `x ∉ interior A`, since `x ∈ A \ interior A`.
    have hx_not_intA : x ∉ interior (A : Set X) := (hUsub hxU).2
    exact (hx_not_intA hx_intA).elim
  · exact Set.empty_subset _

theorem interior_interior_closure_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (interior (closure (A : Set X))) = interior (closure A) := by
  simpa using interior_interior (closure (A : Set X))

theorem closure_eq_univ_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- Prove the inclusion `closure A ⊆ univ`, which is trivial.
  have h₁ : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro _ _
    trivial
  -- Prove the reverse inclusion `univ ⊆ closure A`.
  have h₂ : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    intro x _
    -- Since `closure (interior A) = univ`, every `x` belongs to it.
    have hxInt : x ∈ closure (interior (A : Set X)) := by
      have : x ∈ (Set.univ : Set X) := by
        trivial
      simpa [h] using this
    -- Use monotonicity of `closure` to deduce `x ∈ closure A`.
    have hsubset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      Topology.closure_interior_subset_closure (X := X) A
    exact hsubset hxInt
  exact le_antisymm h₁ h₂

theorem interior_inter_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) = interior A ∩ interior B := by
  apply le_antisymm
  ·
    exact interior_inter_subset (X := X) (A := A) (B := B)
  ·
    exact interior_interiors_subset_interior_inter (X := X) (A := A) (B := B)

theorem closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxCl, hxInt⟩
  -- We show `x ∈ closure (A ∩ B)` using the characterization via open neighborhoods.
  have : x ∈ closure (A ∩ B : Set X) := by
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighborhood `U ∩ interior B` of `x`.
    have hVopen : IsOpen (U ∩ interior B) := hUopen.inter isOpen_interior
    have hxV : x ∈ U ∩ interior B := ⟨hxU, hxInt⟩
    -- Since `x ∈ closure A`, this neighborhood meets `A`.
    have h_non : ((U ∩ interior B) ∩ (A : Set X)).Nonempty := by
      have hClosure := (mem_closure_iff).1 hxCl
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        using hClosure (U ∩ interior B) hVopen hxV
    -- Extract a witness in `U ∩ (A ∩ B)`.
    rcases h_non with ⟨y, hy⟩
    rcases hy with ⟨⟨hyU, hyIntB⟩, hyA⟩
    have hyB : y ∈ B := interior_subset hyIntB
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this

theorem P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (X := X) (closure (A : Set X))) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3] at *
  intro x hxA
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  have hx_int : x ∈ interior (closure (closure (A : Set X))) := h hx_cl
  simpa [closure_closure] using hx_int

theorem P1_union_five {X : Type*} [TopologicalSpace X] {A B C D E : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E) := by
  -- First, combine the properties for `A`, `B`, `C`, and `D`.
  have hABCD : Topology.P1 (X := X) (A ∪ B ∪ C ∪ D) :=
    Topology.P1_union_four (X := X) (A := A) (B := B) (C := C) (D := D)
      hA hB hC hD
  -- Then, unite the result with `E`.
  have hABCDE : Topology.P1 (X := X) ((A ∪ B ∪ C ∪ D) ∪ E) :=
    Topology.P1_union (X := X) (A := A ∪ B ∪ C ∪ D) (B := E) hABCD hE
  -- Re-associate the unions to match the target expression.
  simpa [Set.union_assoc] using hABCDE

theorem interior_inter_closure_subset_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We will show `x ∈ closure (A ∩ B)` using the neighbourhood
  -- characterization of the closure.
  have : x ∈ closure (A ∩ B : Set X) := by
    -- Apply `mem_closure_iff`.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Since `x ∈ interior A`, pick an open `V ⊆ A` with `x ∈ V`.
    rcases mem_interior.1 hxIntA with ⟨V, hVsubA, hVopen, hxV⟩
    -- Consider the open neighbourhood `W = U ∩ V` of `x`.
    have hWopen : IsOpen (U ∩ V) := hUopen.inter hVopen
    have hxW : x ∈ U ∩ V := ⟨hxU, hxV⟩
    -- Because `x ∈ closure B`, this neighbourhood meets `B`.
    have hNon : ((U ∩ V) ∩ (B : Set X)).Nonempty := by
      have hClosure := (mem_closure_iff).1 hxClB
      have : ((U ∩ V) ∩ B).Nonempty := hClosure (U ∩ V) hWopen hxW
      -- Rearrange intersections to match Lean's expectations.
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
    -- Extract a point `y` witnessing the non-emptiness.
    rcases hNon with ⟨y, ⟨⟨hyU, hyV⟩, hyB⟩⟩
    -- `y ∈ V ⊆ A`, hence `y ∈ A ∩ B` and `y ∈ U`.
    have hyA : y ∈ A := hVsubA hyV
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this

theorem closure_interior_closure_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- One direction is given by a general subset lemma.
  have h₁ :
      closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
    Topology.closure_interior_closure_subset_closure (X := X) (A := A)
  -- For the reverse inclusion, rewrite `closure A` using `P1`
  -- and use monotonicity of `closure`.
  have hEq :
      closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  have h₂ :
      closure (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
    intro x hx
    -- View `x` as lying in `closure (interior A)` via the equality `hEq`.
    have hx' : x ∈ closure (interior A) := by
      simpa [hEq] using hx
    -- Use the monotonicity lemma to lift membership to the desired set.
    have hsubset :
        closure (interior A) ⊆
          closure (interior (closure (A : Set X))) :=
      Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A)
    exact hsubset hx'
  exact le_antisymm h₁ h₂

theorem closure_inter_eq_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure (A ∩ B : Set X) = A ∩ B := by
  have hClosed : IsClosed ((A ∩ B : Set X)) := hA.inter hB
  simpa using hClosed.closure_eq

theorem P1_of_closure_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A := by
  -- First obtain `P2` from the density assumption.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_closure_dense_interior (X := X) (A := A) h
  -- Then derive `P1` from `P2`.
  exact Topology.P2_implies_P1 (X := X) (A := A) hP2

theorem P3_union_six {X : Type*} [TopologicalSpace X] {A B C D E F : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) (hF : Topology.P3 (X := X) F) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) := by
  -- First, combine the properties for the first five sets.
  have hABCDE :
      Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E) :=
    Topology.P3_union_five (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E)
      hA hB hC hD hE
  -- Unite the result with `F`.
  have hABCDEF :
      Topology.P3 (X := X) ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) :=
    Topology.P3_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E) (B := F)
      hABCDE hF
  -- Re-associate the unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEF

theorem interior_closure_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  exact interior_subset

theorem isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    IsOpen A :=
  ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3)

theorem interior_closure_eq_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure A))) := by
  -- `P3` gives an equality between the two closures.
  have h :=
    Topology.closure_eq_closure_interior_closure_of_P3
      (X := X) (A := A) hA
  -- Taking `interior` of both sides yields the desired result.
  simpa using congrArg interior h

theorem P2_union_six {X : Type*} [TopologicalSpace X] {A B C D E F : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) (hF : Topology.P2 (X := X) F) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) := by
  -- Combine the properties for the first five sets.
  have hABCDE : Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E) :=
    Topology.P2_union_five (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E)
      hA hB hC hD hE
  -- Unite the resulting set with `F`.
  have hABCDEF : Topology.P2 (X := X) ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) :=
    Topology.P2_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E) (B := F)
      hABCDE hF
  -- Re‐associate the unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEF

theorem interior_eq_empty_of_closure_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = (∅ : Set X)) :
    interior (A : Set X) = (∅ : Set X) := by
  -- First, show `interior A ⊆ ∅`.
  have hsub : interior (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    -- Any point of `interior A` lies in `closure (interior A)`.
    have hx' : x ∈ closure (interior (A : Set X)) := subset_closure hx
    -- Rewrite using the hypothesis that this closure is empty.
    simpa [h] using hx'
  -- The reverse inclusion `∅ ⊆ interior A` is trivial.
  exact le_antisymm hsub (Set.empty_subset _)

theorem isClosed_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (A : Set X))))

theorem closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA
  | inr hxB =>
      have hsubset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB

theorem P1_union_six {X : Type*} [TopologicalSpace X] {A B C D E F : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) := by
  -- Combine the properties for the first five sets.
  have hABCDE :
      Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E) :=
    Topology.P1_union_five (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E)
      hA hB hC hD hE
  -- Unite the result with `F`.
  have hABCDEF :
      Topology.P1 (X := X) ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E) (B := F)
      hABCDE hF
  -- Re-associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABCDEF

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hxInt
  -- From `x ∈ interior A` we infer `x ∈ A`.
  have hxA : x ∈ (A : Set X) := interior_subset hxInt
  -- The set `A` is contained in its closure.
  have : (A : Set X) ⊆ closure (A : Set X) := subset_closure
  -- Therefore, `x ∈ closure A`.
  exact this hxA

theorem closure_interior_subset_of_subset_closed
    {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hAC : (A : Set X) ⊆ C) (hC_closed : IsClosed (C : Set X)) :
    closure (interior (A : Set X)) ⊆ C := by
  -- First, note `interior A ⊆ A ⊆ C`.
  have h₁ : (interior (A : Set X) : Set X) ⊆ C :=
    interior_subset.trans hAC
  -- Taking closures preserves inclusions; rewrite using `closure C = C`
  -- because `C` is closed.
  simpa [hC_closed.closure_eq] using closure_mono h₁

theorem interior_diff_subset_interior_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A \ closure B := by
  intro x hx
  rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
  -- `x` belongs to the interior of `A`
  have hUsubA : (U : Set X) ⊆ A := by
    intro y hy
    exact (hUsub hy).1
  have hx_intA : x ∈ interior A :=
    mem_interior.2 ⟨U, hUsubA, hUopen, hxU⟩
  -- `x` does not belong to the closure of `B`
  have hx_notClB : x ∉ closure B := by
    intro hxClB
    -- Using the neighbourhood `U`, derive a contradiction with `U ⊆ A \ B`
    have hNon : ((U : Set X) ∩ B).Nonempty :=
      (mem_closure_iff).1 hxClB U hUopen hxU
    rcases hNon with ⟨y, ⟨hyU, hyB⟩⟩
    have : y ∉ B := (hUsub hyU).2
    exact this hyB
  exact ⟨hx_intA, hx_notClB⟩

theorem closure_interior_inter_eq_closure_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) =
      closure (interior (A : Set X) ∩ interior B) := by
  apply le_antisymm
  ·
    exact
      Topology.closure_interior_inter_subset_closure_interiors
        (X := X) (A := A) (B := B)
  ·
    exact
      Topology.closure_inter_interior_subset_closure_interior_inter
        (X := X) (A := A) (B := B)

theorem P1_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = A) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hxA
  have : x ∈ closure (interior (A : Set X)) := by
    have : x ∈ (A : Set X) := hxA
    simpa [h] using this
  exact this

theorem closure_union_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure (A ∪ B : Set X) = A ∪ B := by
  have hClosed : IsClosed ((A ∪ B : Set X)) := hA.union hB
  simpa using hClosed.closure_eq

theorem P2_interior_empty_implies_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hInt : interior (A : Set X) = (∅ : Set X)) :
    (A : Set X) = (∅ : Set X) := by
  apply le_antisymm
  · intro x hxA
    have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    simpa [hInt] using hx
  · exact Set.empty_subset _

theorem closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) = (∅ : Set X) ↔
      interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro h
    -- Since `interior A ⊆ closure (interior A)`, the closure being empty
    -- forces `interior A` itself to be empty.
    have hsub : (interior (A : Set X) : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ closure (interior (A : Set X)) := subset_closure hx
      simpa [h] using this
    exact le_antisymm hsub (Set.empty_subset _)
  · intro h
    -- If `interior A` is empty, its closure is also empty.
    simpa [h, closure_empty] using rfl

theorem interior_nonempty_iff_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    (interior (A : Set X)).Nonempty ↔ (A : Set X).Nonempty := by
  constructor
  · intro hInt
    exact hInt.mono (interior_subset : interior (A : Set X) ⊆ A)
  · intro hA
    exact Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA

theorem interior_diff_self_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior ((A : Set X) \ A) = (∅ : Set X) := by
  simp

theorem closure_inter_interior_subset_closure_inter' {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxIntB⟩
  -- We will show `x ∈ closure (A ∩ B)` via the neighbourhood
  -- characterisation of the closure.
  have : x ∈ closure (A ∩ B : Set X) := by
    -- Reformulate membership in the closure.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighbourhood `U ∩ interior B` of `x`.
    have hVopen : IsOpen (U ∩ interior B) := hUopen.inter isOpen_interior
    have hxV : x ∈ U ∩ interior B := ⟨hxU, hxIntB⟩
    -- As `x ∈ closure A`, this neighbourhood meets `A`.
    have hNon : ((U ∩ interior B) ∩ (A : Set X)).Nonempty := by
      have h := (mem_closure_iff).1 hxClA
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        using h (U ∩ interior B) hVopen hxV
    -- Extract a witness `y` in the intersection.
    rcases hNon with ⟨y, ⟨⟨hyU, hyIntB⟩, hyA⟩⟩
    -- `y` also lies in `B` since it is in `interior B`.
    have hyB : y ∈ B := interior_subset hyIntB
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this

theorem interior_inter_of_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    interior (A ∩ B : Set X) = A ∩ interior B := by
  -- We establish both inclusions and then apply `le_antisymm`.
  apply le_antisymm
  · -- `interior (A ∩ B) ⊆ A ∩ interior B`
    intro x hx
    have hxA : x ∈ A := by
      -- `interior (A ∩ B) ⊆ interior A = A` because `A` is open.
      have : x ∈ interior A :=
        (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
      simpa [hA.interior_eq] using this
    have hxIntB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    exact ⟨hxA, hxIntB⟩
  · -- `A ∩ interior B ⊆ interior (A ∩ B)`
    intro x hx
    rcases hx with ⟨hxA, hxIntB⟩
    -- The set `U = A ∩ interior B` is an open neighborhood of `x`
    -- contained in `A ∩ B`.
    have hUopen : IsOpen (A ∩ interior B : Set X) :=
      hA.inter isOpen_interior
    have hUsub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨hy.1, interior_subset hy.2⟩
    have hxU : x ∈ (A ∩ interior B : Set X) := ⟨hxA, hxIntB⟩
    exact (mem_interior.2 ⟨A ∩ interior B, hUsub, hUopen, hxU⟩)

theorem interior_inter_of_open_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = interior A ∩ B := by
  -- Apply the “left‐open” version to the swapped intersection.
  have h :=
    interior_inter_of_open_left (X := X) (A := B) (B := A) hB
  -- Rewrite using commutativity of `∩`.
  simpa [Set.inter_comm] using h

theorem interior_closure_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro x hx
  -- Rewrite the membership using the equality provided by `P2`.
  have hEq := Topology.interior_closure_eq_of_P2 (X := X) (A := A) h
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [hEq] using hx
  -- Use `interior_subset` to step from the interior to the closure.
  exact interior_subset hx'

theorem closure_inter_interior_subset_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ interior B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `closure A`
  have hA : (A ∩ interior B : Set X) ⊆ A := Set.inter_subset_left
  have hxA : x ∈ closure A := (closure_mono hA) hx
  -- `closure B`
  have hB : (A ∩ interior B : Set X) ⊆ B := by
    intro y hy
    exact interior_subset hy.2
  have hxB : x ∈ closure B := (closure_mono hB) hx
  exact ⟨hxA, hxB⟩

theorem subset_closure_interior_of_subset_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : Topology.P1 (X := X) B) (hAB : A ⊆ B) :
    A ⊆ closure (interior B) := by
  intro x hxA
  exact hB (hAB hxA)

theorem P2_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ interior (A : Set X) = A := by
  have h1 := Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hA_closed
  have h2 := Topology.P3_iff_interior_eq_self_of_isClosed (X := X) (A := A) hA_closed
  exact h1.trans h2

theorem IsOpen.diff {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsClosed (B : Set X)) :
    IsOpen (A \ B) := by
  simpa [Set.diff_eq] using hA.inter hB.isOpen_compl

theorem P1_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsClosed (B : Set X)) :
    Topology.P1 (X := X) (A \ B) := by
  -- `A \ B` is open because it is the difference of an open set and a closed set.
  have hOpen : IsOpen ((A \ B) : Set X) :=
    IsOpen.diff (X := X) (A := A) (B := B) hA hB
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A \ B) hOpen

theorem P1_closure_subset_of_superset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1 : Topology.P1 (X := X) A) (hSub : closure (interior A) ⊆ B) :
    closure (A : Set X) ⊆ B := by
  intro x hx
  have hx' : x ∈ closure (interior A) := by
    have hsubset := Topology.P1_closure_subset (X := X) (A := A) hP1
    exact hsubset hx
  exact hSub hx'

theorem interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior (A : Set X) := by
  exact interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)

theorem closure_union_three_subset {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A : Set X) ∪ closure B ∪ closure C ⊆ closure (A ∪ B ∪ C) := by
  intro x hx
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hxA =>
          -- Case `x ∈ closure A`
          have hsubset : (A : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inl hy)
          exact (closure_mono hsubset) hxA
      | inr hxB =>
          -- Case `x ∈ closure B`
          have hsubset : (B : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inr hy)
          exact (closure_mono hsubset) hxB
  | inr hxC =>
      -- Case `x ∈ closure C`
      have hsubset : (C : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inr hy
      exact (closure_mono hsubset) hxC

theorem closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A \ interior B := by
  intro x hx
  -- `x` lies in `closure A` because `A \ B ⊆ A`.
  have hx_clA : x ∈ closure (A : Set X) := by
    have hsubset : (A \ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact (closure_mono hsubset) hx
  -- Show `x ∉ interior B`; otherwise reach a contradiction.
  have hx_not_intB : x ∉ interior B := by
    intro hx_intB
    -- Use the neighbourhood characterization of the closure.
    have hmem := (mem_closure_iff).1 hx
    have hNon : ((interior B : Set X) ∩ (A \ B : Set X)).Nonempty :=
      hmem (interior B) isOpen_interior hx_intB
    rcases hNon with ⟨y, ⟨hy_intB, hy_A_diff_B⟩⟩
    have hy_in_B : y ∈ B := interior_subset hy_intB
    exact hy_A_diff_B.2 hy_in_B
  exact ⟨hx_clA, hx_not_intB⟩

theorem interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (interior (A : Set X)).Nonempty ↔ (A : Set X).Nonempty := by
  constructor
  · intro hInt
    exact hInt.mono (interior_subset : interior (A : Set X) ⊆ A)
  · intro hA
    exact
      Topology.interior_nonempty_of_P2
        (X := X) (A := A) hP2 hA

theorem interior_diff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = interior A \ B := by
  ext x
  constructor
  · intro hx
    have h := interior_diff_subset_interior_diff_closure
        (X := X) (A := A) (B := B) hx
    simpa [hB.closure_eq] using h
  · rintro ⟨hxIntA, hxNotB⟩
    -- `interior A` is open and contains `x`.
    rcases mem_interior.1 hxIntA with ⟨U, hUsubA, hUopen, hxU⟩
    -- The complement of the closed set `B` is open and contains `x`.
    have hOpenCompl : IsOpen ((Bᶜ : Set X)) := hB.isOpen_compl
    have hxComplB : x ∈ (Bᶜ : Set X) := by
      simpa using hxNotB
    -- The intersection `U ∩ Bᶜ` is an open neighborhood of `x`
    -- contained in `A \ B`.
    have hOpenInt : IsOpen (U ∩ (Bᶜ : Set X)) := hUopen.inter hOpenCompl
    have hxInt : x ∈ U ∩ (Bᶜ : Set X) := ⟨hxU, hxComplB⟩
    have hSub :
        (U ∩ (Bᶜ : Set X) : Set X) ⊆ A \ B := by
      intro y hy
      exact ⟨hUsubA hy.1, hy.2⟩
    exact mem_interior.2 ⟨U ∩ (Bᶜ : Set X), hSub, hOpenInt, hxInt⟩

theorem P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) A := by
  -- From the closedness of `A` and the hypothesis `P3`, we derive that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem closure_interior_iterate_six {X : Type*} [TopologicalSpace X] (A : Set X) :
    Nat.iterate (fun S : Set X => closure (interior S)) 6 A =
      closure (interior A) := by
  simp [Nat.iterate, Topology.closure_interior_idempotent]

theorem isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior A) := by
  have h₁ : IsClosed (closure (A : Set X)) := isClosed_closure
  have h₂ : IsClosed ((interior (A : Set X))ᶜ) := by
    simpa using (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  simpa [Set.diff_eq, Set.inter_comm] using h₁.inter h₂

theorem interior_closure_iterate {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure S)) (n.succ) A =
      interior (closure A) := by
  -- Define the idempotent function `f := interior ∘ closure`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- `f` is idempotent.
  have h_idemp : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.interior_closure_idempotent (X := X) (A := S)
  -- A helper lemma: iterating an idempotent function on a fixed point
  -- leaves the point unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih =>
        simp [Nat.iterate, hfix, ih]
  -- Main proof by cases on `n`.
  cases n with
  | zero =>
      -- `Nat.iterate f 1 A = f A`
      simp [Nat.iterate, f]
  | succ k =>
      -- First, iterate starting from the fixed point `f A`.
      have h1 : Nat.iterate f (Nat.succ k) (f A) = f A := by
        have hfix : f (f A) = f A := h_idemp A
        exact iterate_fixed hfix (Nat.succ k)
      -- Unfold one step of the iteration starting from `A`.
      have ht : Nat.iterate f (Nat.succ (Nat.succ k)) A = f A := by
        -- By definition of `Nat.iterate`.
        change Nat.iterate f (Nat.succ k) (f A) = f A
        simpa using h1
      -- Rewrite `f A` back to `interior (closure A)`.
      simpa [f] using ht

theorem interior_closure_nonempty_iff_nonempty_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X := X) A) :
    (interior (closure (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    exact
      Topology.nonempty_of_interior_closure_nonempty
        (X := X) (A := A) hInt
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P3
        (X := X) (A := A) hP3 hA

theorem closure_interior_iterate {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior S)) (n.succ) A =
      closure (interior A) := by
  -- Define `f := closure ∘ interior`.
  let f : Set X → Set X := fun S => closure (interior S)
  -- `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.closure_interior_idempotent (X := X) (A := S)
  -- Iterating an idempotent function on a fixed point leaves it unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewrite the desired iterate so it starts from the fixed point `f A`.
  have h1 : Nat.iterate f (n.succ) A = Nat.iterate f n (f A) := by
    simp [Nat.iterate]
  -- Since `f A` is fixed, the right-hand side simplifies to `f A`.
  have h2 : Nat.iterate f n (f A) = f A := by
    have hfix : f (f A) = f A := hf_id A
    exact (iterate_fixed hfix) n
  -- Assemble the equalities and unfold `f`.
  have : Nat.iterate f (n.succ) A = f A := by
    simpa [h1, h2]
  simpa [f] using this

theorem IsClosed.diff {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsOpen (B : Set X)) :
    IsClosed (A \ B) := by
  simpa [Set.diff_eq] using hA.inter hB.isClosed_compl

theorem closure_union_compl_eq_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ closure ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases hA : x ∈ (A : Set X)
    · exact Or.inl (subset_closure hA)
    · have hAc : x ∈ ((A : Set X)ᶜ) := by
        simpa using hA
      exact Or.inr (subset_closure hAc)

theorem subset_inter_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hP3 : Topology.P3 (X := X) A) :
    A ⊆ closure (interior A) ∩ interior (closure A) := by
  intro x hxA
  exact ⟨hP1 hxA, hP3 hxA⟩

theorem closure_interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- First, note that `A \ B ⊆ A`.
  have h₁ : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Hence `interior (A \ B) ⊆ interior A` by monotonicity of `interior`.
  have h₂ : interior (A \ B : Set X) ⊆ interior A :=
    interior_mono h₁
  -- Taking closures preserves inclusions.
  exact closure_mono h₂

theorem interior_closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure A) := by
  -- Since `A \ B ⊆ A`, their closures satisfy the same inclusion.
  have hsubset : closure (A \ B : Set X) ⊆ closure A :=
    closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)
  -- Monotonicity of `interior` yields the desired result.
  exact interior_mono hsubset

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsClosed (B : Set X)) :
    P2 (X := X) (A \ B) := by
  -- `A \ B` is open because it is the difference of an open and a closed set.
  have hOpen : IsOpen ((A \ B : Set X)) :=
    IsOpen.diff (X := X) (A := A) (B := B) hA hB
  -- Every open set satisfies `P2`.
  exact isOpen_implies_P2 (X := X) (A := A \ B) hOpen

theorem closure_interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (closure (interior (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hCl
    exact
      Topology.nonempty_of_closure_interior_nonempty
        (X := X) (A := A) hCl
  · intro hA
    exact
      Topology.closure_interior_nonempty_of_P2
        (X := X) (A := A) hP2 hA

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsClosed (B : Set X)) :
    Topology.P3 (X := X) (A \ B) := by
  -- The difference of an open set and a closed set is open.
  have hOpen : IsOpen ((A \ B) : Set X) :=
    IsOpen.diff (X := X) (A := A) (B := B) hA hB
  -- Every open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A \ B) hOpen

theorem closure_diff_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B : Set X) ∩ interior B = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxCl, hxInt⟩
    have h : x ∈ closure A \ interior B :=
      (closure_diff_subset (A := A) (B := B)) hxCl
    exact (h.2 hxInt).elim
  · intro hx
    cases hx

theorem P1_and_P3_iff_subset_inter {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) ↔
      (A ⊆ closure (interior A) ∩ interior (closure A)) := by
  constructor
  · intro h
    exact
      subset_inter_of_P1_and_P3 (X := X) (A := A) h.1 h.2
  · intro hSub
    have hP1 : Topology.P1 (X := X) A := by
      dsimp [Topology.P1] at *
      intro x hxA
      exact (hSub hxA).1
    have hP3 : Topology.P3 (X := X) A := by
      dsimp [Topology.P3] at *
      intro x hxA
      exact (hSub hxA).2
    exact ⟨hP1, hP3⟩

theorem isOpen_inter_implies_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (X := X) (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact Topology.isOpen_implies_P2 (X := X) (A := A ∩ B) hOpen

theorem subset_inter_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (A : Set X) ⊆ closure (interior A) ∩ interior (closure (interior A)) := by
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hxCl : x ∈ closure (interior A) := interior_subset hxInt
  exact ⟨hxCl, hxInt⟩

theorem closure_interior_iterate_fixed {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior S)) n (closure (interior A)) =
      closure (interior A) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Nat.iterate, ih,
        Topology.closure_interior_idempotent (X := X) (A := interior A)]

theorem interior_closure_iterate_fixed {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure S)) n (interior (closure A)) =
      interior (closure A) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Nat.iterate, ih,
        Topology.interior_closure_idempotent (X := X) (A := A)]

theorem interior_closure_iterate_from_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure S)) (n.succ) (closure (A : Set X)) =
      interior (closure A) := by
  -- Define `f := interior ∘ closure`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.interior_closure_idempotent (X := X) (A := S)
  -- Helper: a fixed point remains fixed under any number of iterations.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Compute `f (closure A)`.
  have hfc : f (closure (A : Set X)) = interior (closure A) := by
    dsimp [f]
    simpa [closure_closure]
  -- `interior (closure A)` is a fixed point of `f`.
  have hfix_int : f (interior (closure A)) = interior (closure A) := by
    dsimp [f]
    simpa using
      Topology.interior_closure_idempotent (X := X) (A := closure A)
  -- Rewrite the desired iterate in terms of the fixed point and simplify.
  calc
    Nat.iterate f (n.succ) (closure (A : Set X))
        = Nat.iterate f n (f (closure (A : Set X))) := by
          simp [Nat.iterate]
    _ = Nat.iterate f n (interior (closure A)) := by
          simpa [hfc]
    _ = interior (closure A) := by
          simpa using (iterate_fixed hfix_int n)

theorem closure_union_interior_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ B : Set X) = closure (interior A) ∪ closure B := by
  simpa using closure_union (interior A) B

theorem closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxCl, hxInt⟩
    rcases mem_interior.1 hxInt with ⟨U, hUsub, hUopen, hxU⟩
    have hNon : ((U : Set X) ∩ (A : Set X)).Nonempty := by
      have hClosure := (mem_closure_iff).1 hxCl
      exact hClosure U hUopen hxU
    rcases hNon with ⟨y, ⟨hyU, hyA⟩⟩
    have hyCompl : y ∈ ((A : Set X)ᶜ) := hUsub hyU
    have : False := hyCompl hyA
    exact this.elim
  · intro hx
    cases hx

theorem interior_closure_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (interior (closure (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    exact
      Topology.nonempty_of_interior_closure_nonempty
        (X := X) (A := A) hInt
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P2
        (X := X) (A := A) hP2 hA

theorem closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ interior (A : Set X) = closure (A : Set X) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hCl => exact hCl
    | inr hInt =>
        have hsubset : (interior (A : Set X) : Set X) ⊆ closure (A : Set X) :=
          interior_subset_closure (X := X) (A := A)
        exact hsubset hInt
  · intro hx
    exact Or.inl hx

theorem closure_interior_nonempty_iff_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    (closure (interior (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · exact Topology.nonempty_of_closure_interior_nonempty (X := X) (A := A)
  · exact Topology.closure_interior_nonempty_of_P1 (X := X) (A := A) hP1

theorem isOpen_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ Topology.P3 (X := X) (closure (A : Set X)) := by
  -- `closure A` is closed.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- Use the existing equivalence between `P3` and openness for closed sets.
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X)
      (A := closure (A : Set X)) hClosed).symm

theorem closure_subset_closure_interior_of_subset_and_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1B : Topology.P1 (X := X) B) (hAB : (A : Set X) ⊆ B) :
    closure (A : Set X) ⊆ closure (interior B) := by
  calc
    closure (A : Set X) ⊆ closure B := closure_mono hAB
    _ ⊆ closure (interior B) := by
      have h : (B : Set X) ⊆ closure (interior B) := hP1B
      have h' : closure (B : Set X) ⊆ closure (closure (interior B)) :=
        closure_mono h
      simpa [closure_closure] using h'

theorem interior_union_closure_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hIntA =>
      -- First case: `x ∈ interior A`.
      -- Upgrade to `x ∈ interior (closure A)`.
      have hIntClA : x ∈ interior (closure A) :=
        (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hIntA
      -- `closure A ⊆ closure (A ∪ B)`.
      have hsubset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Hence the desired membership follows by monotonicity of `interior`.
      exact (interior_mono hsubset) hIntClA
  | inr hIntClB =>
      -- Second case: `x ∈ interior (closure B)`.
      -- `closure B ⊆ closure (A ∪ B)`.
      have hsubset : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Conclude using monotonicity of `interior`.
      exact (interior_mono hsubset) hIntClB

theorem interior_inter_closure_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ closure ((A : Set X)ᶜ) = (∅ : Set X) := by
  classical
  -- We show that the intersection contains no points.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hxInt, hxCl⟩
  -- Pick an open neighborhood `U` of `x` contained in `A`.
  rcases mem_interior.1 hxInt with ⟨U, hUsubA, hUopen, hxU⟩
  -- Because `x ∈ closure (Aᶜ)`, the neighborhood `U` meets `Aᶜ`.
  have hNon : ((U : Set X) ∩ ((A : Set X)ᶜ)).Nonempty :=
    (mem_closure_iff).1 hxCl U hUopen hxU
  rcases hNon with ⟨y, ⟨hyU, hyCompl⟩⟩
  -- But `U ⊆ A`, so `y ∈ A`, contradicting `y ∈ Aᶜ`.
  exact hyCompl (hUsubA hyU)

theorem subset_interior_closure_of_subset_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP3B : Topology.P3 (X := X) B) (hAB : A ⊆ B) :
    A ⊆ interior (closure B) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  exact hP3B hxB

theorem isClosed_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) ⊆ A) : IsClosed (A : Set X) := by
  have hEq : closure (A : Set X) = A := by
    apply le_antisymm
    · exact h
    · exact subset_closure
  simpa [hEq] using (isClosed_closure : IsClosed (closure (A : Set X)))

theorem isClosed_closure_diff_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior (closure (A : Set X))) := by
  -- `closure A` is closed.
  have hClosedCl : IsClosed (closure (A : Set X)) := isClosed_closure
  -- The complement of an open set is closed; here the open set is `interior (closure A)`.
  have hClosedCompl : IsClosed ((interior (closure (A : Set X)))ᶜ) :=
    (isOpen_interior : IsOpen (interior (closure (A : Set X)))).isClosed_compl
  -- The desired set is the intersection of these two closed sets.
  simpa [Set.diff_eq] using hClosedCl.inter hClosedCompl

theorem P3_iff_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A ↔ A ⊆ interior (closure (A : Set X)) := by
  rfl

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2] at *
  intro x hxA
  -- From `P3` we know that `x ∈ interior (closure A)`.
  have hx_int_clA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- `P1` yields `closure A ⊆ closure (interior A)`.
  have h_closure_subset :
      closure (A : Set X) ⊆ closure (interior A) :=
    Topology.P1_closure_subset (X := X) (A := A) hP1
  -- Monotonicity of `interior` then gives the required inclusion.
  have h_int_subset :
      interior (closure (A : Set X)) ⊆ interior (closure (interior A)) :=
    interior_mono h_closure_subset
  exact h_int_subset hx_int_clA

theorem interior_closure_inter_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X)) ∩ closure (interior A) ⊆ closure A := by
  intro x hx
  exact (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hx.1

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A ↔ (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1_and_P3 (X := X) (A := A) hP2
  · rintro ⟨hP1, hP3⟩
    exact Topology.P1_and_P3_implies_P2 (X := X) (A := A) hP1 hP3

theorem P2_union_seven {X : Type*} [TopologicalSpace X]
    {A B C D E F G : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) (hF : Topology.P2 (X := X) F)
    (hG : Topology.P2 (X := X) G) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) := by
  -- Combine the first five sets.
  have hABCDE :
      Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E) :=
    Topology.P2_union_five (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E)
      hA hB hC hD hE
  -- Unite the result with `F`.
  have hABCDEF :
      Topology.P2 (X := X) ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) :=
    Topology.P2_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E) (B := F)
      hABCDE hF
  -- Unite the result with `G`.
  have hABCDEFG :
      Topology.P2 (X := X) (((A ∪ B ∪ C ∪ D ∪ E) ∪ F) ∪ G) :=
    Topology.P2_union (X := X)
      (A := (A ∪ B ∪ C ∪ D ∪ E) ∪ F) (B := G)
      hABCDEF hG
  -- Re‐associate the unions to match the desired shape.
  simpa [Set.union_assoc] using hABCDEFG

theorem P3_union_seven {X : Type*} [TopologicalSpace X] {A B C D E F G : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) (hF : Topology.P3 (X := X) F)
    (hG : Topology.P3 (X := X) G) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) := by
  -- Combine the properties for the first six sets.
  have hABCDEF :
      Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) :=
    Topology.P3_union_six (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      hA hB hC hD hE hF
  -- Unite the result with `G`.
  have hABCDEFG :
      Topology.P3 (X := X) ((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G) :=
    Topology.P3_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F) (B := G)
      hABCDEF hG
  -- Reassociate unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEFG

theorem P1_union_seven {X : Type*} [TopologicalSpace X] {A B C D E F G : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F)
    (hG : Topology.P1 (X := X) G) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) := by
  -- Combine the properties for the first six sets.
  have hABCDEF :
      Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) :=
    Topology.P1_union_six (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      hA hB hC hD hE hF
  -- Unite the result with `G`.
  have hABCDEFG :
      Topology.P1 (X := X) ((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F) (B := G)
      hABCDEF hG
  -- Re‐associate the unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEFG

theorem closure_union_interior_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ interior B : Set X) = closure A ∪ closure (interior B) := by
  simpa using closure_union (A : Set X) (interior B)

theorem closure_interior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- `P2` gives `closure A = closure (interior A)`.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hP2
  -- We establish the two inclusions separately.
  apply le_antisymm
  · -- Always, `closure (interior (closure A)) ⊆ closure A`.
    exact
      Topology.closure_interior_closure_subset_closure (X := X) (A := A)
  · -- `closure A ⊆ closure (interior (closure A))`, using the equality above.
    have h_subset :
        closure (interior A) ⊆ closure (interior (closure (A : Set X))) :=
      Topology.closure_interior_subset_closure_interior_closure (X := X) (A := A)
    simpa [h_eq] using h_subset

theorem interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro x hx
  have hx_cl : x ∈ closure (A : Set X) := interior_subset hx
  have hsubset : closure (A : Set X) ⊆ closure (interior A) :=
    Topology.P1_closure_subset (X := X) (A := A) hP1
  exact hsubset hx_cl

theorem closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) \ closure (B : Set X) ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotClB⟩
  -- We will show `x ∈ closure (A \ B)` via `mem_closure_iff`.
  have : x ∈ closure (A \ B : Set X) := by
    -- Reformulate membership in the closure using open neighbourhoods.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Choose an open neighbourhood of `x` that avoids `B`.
    let V : Set X := (closure (B : Set X))ᶜ
    have hVopen : IsOpen V := isClosed_closure.isOpen_compl
    have hxV : x ∈ V := by
      dsimp [V]
      exact hxNotClB
    -- The neighbourhood `U ∩ V` is open, contains `x`, and is disjoint from `B`.
    have hWopen : IsOpen (U ∩ V) := hUopen.inter hVopen
    have hxW : x ∈ U ∩ V := ⟨hxU, hxV⟩
    -- Since `x ∈ closure A`, this neighbourhood meets `A`.
    have hNonempty : ((U ∩ V) ∩ (A : Set X)).Nonempty := by
      have h := (mem_closure_iff).1 hxClA
      have h' := h (U ∩ V) hWopen hxW
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h'
    -- Extract a witness `y`.
    rcases hNonempty with ⟨y, ⟨⟨hyU, hyV⟩, hyA⟩⟩
    -- Show that `y ∉ B`.
    have hyNotB : y ∉ B := by
      intro hyB
      have hyClB : y ∈ closure (B : Set X) := subset_closure hyB
      have : y ∈ V := hyV
      dsimp [V] at this
      exact this hyClB
    -- Hence `y ∈ U ∩ (A \ B)`, proving the required non‐emptiness.
    exact ⟨y, ⟨hyU, ⟨hyA, hyNotB⟩⟩⟩
  exact this

theorem interior_closure_interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (interior (closure (interior (A : Set X)))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    -- From a point in the interior we obtain one in the closure.
    have hCl : (closure (interior (A : Set X))).Nonempty := by
      rcases hInt with ⟨x, hx⟩
      exact ⟨x, interior_subset hx⟩
    -- Use an existing lemma to deduce non‐emptiness of `A`.
    exact
      Topology.nonempty_of_closure_interior_nonempty
        (X := X) (A := A) hCl
  · intro hA
    -- Apply the forward implication already available for `P2`.
    exact
      Topology.interior_closure_interior_nonempty_of_P2
        (X := X) (A := A) hP2 hA

theorem closure_interior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    closure (interior A) = closure (A : Set X) := by
  simpa using
    (Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hA).symm

theorem interior_diff_closure_eq {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (A \ closure (B : Set X)) = interior A \ closure B := by
  have hClosed : IsClosed (closure (B : Set X)) := isClosed_closure
  simpa using
    (interior_diff_of_closed (X := X) (A := A) (B := closure (B : Set X)) hClosed)

theorem closure_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A ∪ B ∪ C : Set X) = closure A ∪ closure B ∪ closure C := by
  -- First, group the union so that `closure_union` can be applied.
  have h₁ :
      closure ((A ∪ B) ∪ C : Set X) =
        closure (A ∪ B : Set X) ∪ closure C := by
    simpa using closure_union (A ∪ B : Set X) C
  -- Next, distribute `closure` over `A ∪ B`.
  have h₂ : closure (A ∪ B : Set X) = closure A ∪ closure B := by
    simpa using closure_union (A : Set X) B
  -- Assemble the pieces and tidy up with associativity of `∪`.
  calc
    closure (A ∪ B ∪ C : Set X)
        = closure ((A ∪ B) ∪ C : Set X) := by
            simpa [Set.union_assoc]
    _ = closure (A ∪ B : Set X) ∪ closure C := by
            simpa using h₁
    _ = (closure A ∪ closure B) ∪ closure C := by
            simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C := by
            simpa [Set.union_assoc]

theorem closure_interior_inter_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ closure (interior (closure A)) =
      closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hsubset :
        closure (interior A) ⊆ closure (interior (closure A)) :=
      Topology.closure_interior_subset_closure_interior_closure (X := X) A
    exact ⟨hx, hsubset hx⟩

theorem closure_inter_interior_subset_closure_inter_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B : Set X) ⊆ closure (A ∩ B) := by
  -- Since `interior B ⊆ B`, we have `A ∩ interior B ⊆ A ∩ B`.
  have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨hx.1, interior_subset hx.2⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset

theorem closure_interior_iterate_from_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior S)) (n.succ) (interior A) =
      closure (interior A) := by
  simpa [interior_interior]
    using closure_interior_iterate (X := X) (A := interior A) (n := n)

theorem P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  -- Both properties hold unconditionally under the dense‐interior hypothesis.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_dense_interior (X := X) (A := A) h
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h
  exact ⟨fun _ => hP2, fun _ => hP1⟩

theorem subset_interior_of_closed_superset_of_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP3 : Topology.P3 (X := X) A)
    (hAB : (A : Set X) ⊆ B) (hB : IsClosed (B : Set X)) :
    (A : Set X) ⊆ interior B := by
  intro x hxA
  -- From `P3`, the point lies in `interior (closure A)`.
  have hxIntClA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Since `B` is closed and contains `A`, its closure is itself,
  -- hence `closure A ⊆ B`.
  have hsubset : closure (A : Set X) ⊆ B := by
    have h : closure (A : Set X) ⊆ closure B := closure_mono hAB
    simpa [hB.closure_eq] using h
  -- Monotonicity of `interior` gives the desired inclusion.
  have hIntSubset : interior (closure (A : Set X)) ⊆ interior B :=
    interior_mono hsubset
  exact hIntSubset hxIntClA

theorem P1_union_of_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : (B : Set X) ⊆ closure (interior A)) :
    Topology.P1 (X := X) (A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`.
  have h_mono :
      closure (interior A : Set X) ⊆
        closure (interior (A ∪ B : Set X)) := by
    have h_inner :
        (interior A : Set X) ⊆ interior (A ∪ B) :=
      interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
    exact closure_mono h_inner
  cases hx with
  | inl hxA =>
      -- Case `x ∈ A`.
      exact h_mono (hA hxA)
  | inr hxB =>
      -- Case `x ∈ B`.
      exact h_mono (hB hxB)

theorem closure_union_interior_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure ((A : Set X) ∪ interior A) = closure (A : Set X) := by
  have h : (interior A : Set X) ⊆ A := interior_subset
  have hUnion : (A : Set X) ∪ interior A = A :=
    Set.union_eq_self_of_subset_right h
  simpa [hUnion]

theorem interior_closure_interior_iterate {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure (interior S))) (n.succ) A =
      interior (closure (interior A)) := by
  -- Define `f := interior ∘ closure ∘ interior`.
  let f : Set X → Set X := fun S => interior (closure (interior S))
  -- Show that `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using
      Topology.interior_closure_idempotent_iter (X := X) (A := S)
  -- A helper lemma: iterating an idempotent function on a fixed point leaves it unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewrite the `(n.succ)`-th iterate starting from `A` so that it starts from the fixed point `f A`.
  have h_step : Nat.iterate f (n.succ) A = Nat.iterate f n (f A) := by
    simp [Nat.iterate]
  -- Since `f A` is a fixed point of `f`, the right-hand side simplifies to `f A`.
  have h_iter : Nat.iterate f n (f A) = f A := by
    have hfix : f (f A) = f A := hf_id A
    exact iterate_fixed hfix n
  -- Assemble the equalities and unfold `f`.
  have : Nat.iterate f (n.succ) A = f A := by
    simpa [h_step, h_iter]
  simpa [f] using this

theorem P3_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P3 (X := X) A ↔ Topology.P2 (X := X) A := by
  constructor
  · intro _hP3
    exact Topology.P2_of_dense_interior (X := X) (A := A) h
  · intro _hP2
    exact Topology.P3_of_dense_interior (X := X) (A := A) h

theorem interior_closure_interior_inter_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (A : Set X))) ∩ interior (closure (A : Set X)) =
      interior (closure (interior (A : Set X))) := by
  -- First, note that `interior (closure (interior A)) ⊆ interior (closure A)`.
  have hsubset :
      interior (closure (interior (A : Set X))) ⊆ interior (closure (A : Set X)) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A)
  -- Now prove the desired set equality by double inclusion.
  ext x
  constructor
  · -- The left‐to‐right inclusion is immediate.
    intro hx
    exact hx.1
  · -- For the converse, use the inclusion `hsubset`.
    intro hx
    exact ⟨hx, hsubset hx⟩

theorem P2_iff_P1_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A ↔ Topology.P1 (X := X) A := by
  -- Start with the established equivalence `P2 ↔ P1 ∧ P3`.
  have h₁ := Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  -- Given the assumption `P3 A`, simplify the right side of the equivalence.
  have h₂ :
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) ↔
        Topology.P1 (X := X) A := by
    constructor
    · intro h
      exact h.1
    · intro hP1
      exact ⟨hP1, hP3⟩
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem interior_inter_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hIntA, hIntAc⟩
    have hA : x ∈ (A : Set X) := interior_subset hIntA
    have hAc : x ∈ ((A : Set X)ᶜ) := interior_subset hIntAc
    have hContr : False := hAc hA
    exact False.elim hContr
  · intro hx
    cases hx

theorem closure_interior_iterate_from_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior S)) (n.succ) (closure (A : Set X)) =
      closure (interior (closure (A : Set X))) := by
  -- Define the idempotent map `f := closure ∘ interior`.
  let f : Set X → Set X := fun S => closure (interior S)
  -- `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.closure_interior_idempotent (X := X) (A := S)
  -- A fixed point of an idempotent function remains fixed under iteration.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewrite the desired iterate so that it starts from the fixed point `f (closure A)`.
  have h_step :
      Nat.iterate f (n.succ) (closure (A : Set X)) =
        Nat.iterate f n (f (closure (A : Set X))) := by
    simp [Nat.iterate]
  -- Since `f (closure A)` is a fixed point, the right‐hand side collapses.
  have h_iter :
      Nat.iterate f n (f (closure (A : Set X))) = f (closure (A : Set X)) := by
    have hfix : f (f (closure (A : Set X))) = f (closure (A : Set X)) := by
      simpa using hf_id (closure (A : Set X))
    exact iterate_fixed hfix n
  -- Assemble the pieces and unfold `f`.
  simpa [h_step, h_iter, f]

theorem P1_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  have h₁ := Topology.P1_iff_P2_of_dense_interior (X := X) (A := A) h
  have h₂ := (Topology.P3_iff_P2_of_dense_interior (X := X) (A := A) h).symm
  exact h₁.trans h₂

theorem closure_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    closure (A ∪ B ∪ C ∪ D : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D := by
  -- First, distribute `closure` over `A ∪ B ∪ C`.
  have hABC :
      closure (A ∪ B ∪ C : Set X) =
        closure A ∪ closure B ∪ closure C :=
    closure_union_three (X := X) (A := A) (B := B) (C := C)
  -- Now regroup the unions and apply `closure_union` once more.
  calc
    closure (A ∪ B ∪ C ∪ D : Set X)
        = closure ((A ∪ B ∪ C) ∪ D : Set X) := by
            simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C : Set X) ∪ closure D := by
            simpa using
              closure_union (A := (A ∪ B ∪ C : Set X)) (B := D)
    _ = (closure A ∪ closure B ∪ closure C) ∪ closure D := by
            simpa [hABC]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D := by
            simpa [Set.union_assoc]

theorem interior_subset_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ⊆ closure (interior A) := by
  intro x hx
  exact (subset_closure : (interior (A : Set X) : Set X) ⊆ closure (interior A)) hx

theorem closure_interior_closure_iterate {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior (closure S))) (n.succ) A =
      closure (interior (closure A)) := by
  -- Define the idempotent function `f`.
  let f : Set X → Set X := fun S => closure (interior (closure S))
  -- Show that `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    -- Apply the idempotency lemma to `closure S`.
    simpa using
      Topology.closure_interior_idempotent (X := X) (A := closure S)
  -- A helper lemma: iterating an idempotent function on a fixed point
  -- leaves the point unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewrite the desired iterate so it starts from the fixed point `f A`.
  have h₁ : Nat.iterate f (n.succ) A =
      Nat.iterate f n (f A) := by
    simp [Nat.iterate]
  -- Since `f A` is a fixed point, the right-hand side collapses to `f A`.
  have h₂ : Nat.iterate f n (f A) = f A := by
    have hfix : f (f A) = f A := hf_id A
    exact iterate_fixed hfix n
  -- Assemble the equalities and unfold `f`.
  have : Nat.iterate f (n.succ) A = f A := by
    simpa [h₁, h₂]
  simpa [f] using this

theorem closure_interior_closure_eq_closure_of_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (closure (A : Set X))) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- `closure A` is always a closed set.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- Apply the existing lemma for closed sets satisfying `P2`.
  simpa using
    Topology.closure_interior_eq_self_of_closed_and_P2
      (X := X) (A := closure (A : Set X)) hClosed h

theorem interior_closure_inter_comm {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    interior (closure (A ∩ B : Set X)) =
      interior (closure (B ∩ A : Set X)) := by
  simpa [Set.inter_comm]

theorem closure_interior_diff_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (A : Set X) \ interior B := by
  -- `interior (A \ B)` is contained in `A \ B`.
  have h₁ : (interior (A \ B : Set X) : Set X) ⊆ A \ B :=
    interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior (A \ B : Set X)) ⊆ closure (A \ B) :=
    closure_mono h₁
  -- From an existing lemma we have `closure (A \ B) ⊆ closure A \ interior B`.
  have h₃ :
      closure (A \ B : Set X) ⊆ closure (A : Set X) \ interior B :=
    closure_diff_subset (A := A) (B := B)
  -- Combine the two inclusions.
  exact h₂.trans h₃

theorem closure_union_five {X : Type*} [TopologicalSpace X]
    {A B C D E : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
  -- Regroup the unions so that `closure_union` is applicable.
  have h₁ :
      closure (A ∪ B ∪ C ∪ D ∪ E : Set X) =
        closure ((A ∪ B ∪ C ∪ D) ∪ E : Set X) := by
    simpa [Set.union_assoc]
  -- Distribute `closure` over the last union.
  have h₂ :
      closure ((A ∪ B ∪ C ∪ D) ∪ E : Set X) =
        closure (A ∪ B ∪ C ∪ D : Set X) ∪ closure E := by
    simpa using
      closure_union (A := (A ∪ B ∪ C ∪ D : Set X)) (B := E)
  -- Use the existing four-set lemma.
  have h₃ :
      closure (A ∪ B ∪ C ∪ D : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D := by
    simpa using
      closure_union_four (X := X)
        (A := A) (B := B) (C := C) (D := D)
  -- Combine the equalities and reassociate unions.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E : Set X)
        = closure ((A ∪ B ∪ C ∪ D) ∪ E : Set X) := by
          simpa [Set.union_assoc] using h₁
    _ = closure (A ∪ B ∪ C ∪ D : Set X) ∪ closure E := by
          simpa using h₂
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D) ∪ closure E := by
          simpa [h₃]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
          simpa [Set.union_assoc]

theorem closure_union_six {X : Type*} [TopologicalSpace X]
    {A B C D E F : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F := by
  -- Reassociate the unions so that `closure_union` can be applied.
  have h₁ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) =
        closure ((A ∪ B ∪ C ∪ D ∪ E) ∪ F : Set X) := by
    simpa [Set.union_assoc]
  -- Distribute `closure` over the last union.
  have h₂ :
      closure ((A ∪ B ∪ C ∪ D ∪ E) ∪ F : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E : Set X) ∪ closure F := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E : Set X))
        (B := F)
  -- Use the existing five-set lemma.
  have h₃ :
      closure (A ∪ B ∪ C ∪ D ∪ E : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
    simpa using
      closure_union_five (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E)
  -- Assemble the pieces and tidy up with associativity of `∪`.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X)
        = closure ((A ∪ B ∪ C ∪ D ∪ E) ∪ F : Set X) := by
            simpa [Set.union_assoc] using h₁
    _ = closure (A ∪ B ∪ C ∪ D ∪ E : Set X) ∪ closure F := by
            simpa using h₂
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E) ∪ closure F := by
            simpa [h₃]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F := by
            simpa [Set.union_assoc]

theorem IsClosed.isOpen_compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsClosed (s : Set X)) : IsOpen ((s : Set X)ᶜ) := by
  simpa using (isOpen_compl_iff).2 h

theorem closure_union_seven {X : Type*} [TopologicalSpace X]
    {A B C D E F G : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F ∪ closure G := by
  have h₁ :
      closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) ∪ closure G := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X))
        (B := G)
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F := by
    simpa using
      closure_union_six (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X)
        = closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) ∪ closure G := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F) ∪
          closure G := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F ∪
          closure G := by
          simp [Set.union_assoc]

theorem interior_closure_nonempty_iff_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    (interior (closure (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    exact
      Topology.nonempty_of_interior_closure_nonempty
        (X := X) (A := A) hInt
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P1
        (X := X) (A := A) hP1 hA

theorem isClosed_closure_interior_diff_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X)) \ interior (closure (A : Set X))) := by
  -- `closure (interior A)` is closed.
  have h₁ : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- The complement of the open set `interior (closure A)` is closed.
  have h₂ : IsClosed ((interior (closure (A : Set X)))ᶜ) :=
    (isOpen_interior : IsOpen (interior (closure (A : Set X)))).isClosed_compl
  -- The difference is the intersection of these two closed sets.
  simpa [Set.diff_eq, Set.inter_comm] using h₁.inter h₂



theorem P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  exact
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hClosed).2 hP3

theorem closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
  classical
  ext x
  constructor
  · intro hxCl
    -- We show `x ∉ interior A`
    have hnot : x ∉ interior (A : Set X) := by
      intro hxInt
      -- Choose an open neighbourhood of `x` contained in `A`.
      rcases mem_interior.1 hxInt with ⟨U, hUsubA, hUopen, hxU⟩
      -- Since `x ∈ closure (Aᶜ)`, the neighbourhood `U` meets `Aᶜ`.
      have hNon : ((U : Set X) ∩ ((A : Set X)ᶜ)).Nonempty :=
        (mem_closure_iff).1 hxCl U hUopen hxU
      rcases hNon with ⟨y, ⟨hyU, hyCompl⟩⟩
      have hyA : y ∈ (A : Set X) := hUsubA hyU
      exact hyCompl hyA
    -- Membership in the complement is definitionally `¬`.
    exact hnot
  · intro hxNotInt
    -- `hxNotInt` is a proof that `x ∉ interior A`
    have hxCl : x ∈ closure ((A : Set X)ᶜ) := by
      -- Use the neighbourhood characterisation of the closure.
      refine (mem_closure_iff).2 ?_
      intro U hUopen hxU
      -- We must show `U ∩ Aᶜ` is non‐empty.
      by_cases hNon : ((U : Set X) ∩ ((A : Set X)ᶜ)).Nonempty
      · exact hNon
      · -- If not, then `U ⊆ A`, contradicting `hxNotInt`.
        have hSub : (U : Set X) ⊆ A := by
          intro y hyU
          by_contra hyNotA
          have hyCompl : y ∈ ((A : Set X)ᶜ) := hyNotA
          have : ((U : Set X) ∩ ((A : Set X)ᶜ)).Nonempty :=
            ⟨y, ⟨hyU, hyCompl⟩⟩
          exact (hNon this).elim
        have hxInt : x ∈ interior (A : Set X) :=
          mem_interior.2 ⟨U, hSub, hUopen, hxU⟩
        exact (hxNotInt hxInt).elim
    exact hxCl

theorem closure_union_eight {X : Type*} [TopologicalSpace X]
    {A B C D E F G H : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪
      closure E ∪ closure F ∪ closure G ∪ closure H := by
  -- Distribute `closure` over the last union.
  have h₁ :
      closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ∪ H : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X) ∪ closure H := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X))
        (B := H)
  -- Apply the seven-set lemma.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪
        closure E ∪ closure F ∪ closure G := by
    simpa using
      closure_union_seven (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (G := G)
  -- Assemble the equalities and reassociate unions.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X)
        = closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ∪ H : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G : Set X) ∪ closure H := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G) ∪ closure H := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪
        closure E ∪ closure F ∪ closure G ∪ closure H := by
          simp [Set.union_assoc]

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = (s : Set α) := by
  ext x
  simp

theorem interior_diff_closure_interior_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior ((A : Set X) \ closure (interior A)) = (∅ : Set X) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    -- `U ⊆ A`
    have hUsubA : (U : Set X) ⊆ A := fun y hy => (hUsub hy).1
    -- Hence `U ⊆ interior A`
    have hUsubInt : (U : Set X) ⊆ interior (A : Set X) :=
      interior_maximal hUsubA hUopen
    -- So `x ∈ interior A ⊆ closure (interior A)`
    have hxInClInt : x ∈ closure (interior (A : Set X)) :=
      subset_closure (hUsubInt hxU)
    -- But `x ∉ closure (interior A)` since `U ⊆ (closure (interior A))ᶜ`
    have hxNotClInt : x ∉ closure (interior (A : Set X)) :=
      (hUsub hxU).2
    exact (hxNotClInt hxInClInt).elim
  · exact Set.empty_subset _

theorem P3_union_eight {X : Type*} [TopologicalSpace X] {A B C D E F G H : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) (hF : Topology.P3 (X := X) F)
    (hG : Topology.P3 (X := X) G) (hH : Topology.P3 (X := X) H) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) := by
  -- First, combine the properties for the first seven sets.
  have hABCDEFG :
      Topology.P3 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) :=
    Topology.P3_union_seven (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (G := G)
      hA hB hC hD hE hF hG
  -- Unite the result with `H`.
  have hABCDEFGH :
      Topology.P3 (X := X) ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ∪ H) :=
    Topology.P3_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) (B := H)
      hABCDEFG hH
  -- Re-associate unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEFGH

theorem P2_union_eight {X : Type*} [TopologicalSpace X]
    {A B C D E F G H : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) (hF : Topology.P2 (X := X) F)
    (hG : Topology.P2 (X := X) G) (hH : Topology.P2 (X := X) H) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) := by
  -- Combine the properties for the first seven sets.
  have hABCDEFG :
      Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) :=
    Topology.P2_union_seven (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (G := G)
      hA hB hC hD hE hF hG
  -- Unite the result with `H`.
  have hABCDEFGH :
      Topology.P2 (X := X) ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) ∪ H) :=
    Topology.P2_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G) (B := H)
      hABCDEFG hH
  -- Re‐associate unions to match the desired expression.
  simpa [Set.union_assoc] using hABCDEFGH

theorem interior_closure_union_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure ((A : Set X) ∪ interior A)) = interior (closure (A : Set X)) := by
  have h := Topology.closure_union_interior_self (X := X) (A := A)
  simpa using congrArg interior h

theorem interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ := by
  classical
  -- Apply the complement lemma to `Aᶜ`.
  have h :=
    closure_compl_eq_compl_interior (X := X) (A := (A : Set X)ᶜ)
  -- Rewrite the complements.
  have h' : closure (A : Set X) = (interior ((A : Set X)ᶜ))ᶜ := by
    simpa [Set.compl_compl] using h
  -- Take complements of both sides to obtain the desired equality.
  have h'' : interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ := by
    simpa using (congrArg Set.compl h').symm
  exact h''

theorem interior_union_closure_compl_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  classical
  -- Rewrite `closure (Aᶜ)` using the complement of an interior.
  have h : closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
    simpa using closure_compl_eq_compl_interior (X := X) (A := A)
  -- The desired equality is now immediate.
  calc
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ)
        = interior (A : Set X) ∪ (interior (A : Set X))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (interior (A : Set X))

theorem interior_closure_diff_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X) \ A) = (∅ : Set X) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    -- The point `x` lies in `closure A`, since `U ⊆ closure A \ A ⊆ closure A`.
    have hxCl : x ∈ closure (A : Set X) := by
      have : x ∈ closure (A : Set X) \ A := hUsub hxU
      exact this.1
    -- By the defining property of the closure, every open neighbourhood of `x`
    -- meets `A`, and in particular the neighbourhood `U` does.
    have hNon : ((U : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxCl U hUopen hxU
    -- However, `U ⊆ closure A \ A`, so `U` is disjoint from `A`, a contradiction.
    rcases hNon with ⟨y, ⟨hyU, hyA⟩⟩
    have : y ∉ A := by
      have : y ∈ closure (A : Set X) \ A := hUsub hyU
      exact this.2
    exact (this hyA).elim
  · exact Set.empty_subset _



theorem P1_union_eight {X : Type*} [TopologicalSpace X] {A B C D E F G H : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F)
    (hG : Topology.P1 (X := X) G) (hH : Topology.P1 (X := X) H) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) := by
  -- Combine the first six sets.
  have hABCDEF :
      Topology.P1 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F) :=
    Topology.P1_union_six (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      hA hB hC hD hE hF
  -- Unite the result with `G`.
  have hABCDEFG :
      Topology.P1 (X := X) ((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F) (B := G)
      hABCDEF hG
  -- Finally, unite the result with `H`.
  have hABCDEFGH :
      Topology.P1 (X := X) (((A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G) ∪ H) :=
    Topology.P1_union (X := X)
      (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F) ∪ G) (B := H)
      hABCDEFG hH
  -- Re‐associate the unions to obtain the desired expression.
  simpa [Set.union_assoc] using hABCDEFGH

theorem P1_of_P1_between {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.P1 (X := X) A) (hAB₁ : (A : Set X) ⊆ B)
    (hAB₂ : (B : Set X) ⊆ closure A) :
    Topology.P1 (X := X) B := by
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at *
  intro x hxB
  -- We will prove that `x ∈ closure (interior B)`.
  -- First, show that `x ∈ closure (interior A)`.
  have hx_cl_intA : x ∈ closure (interior A) := by
    by_cases hxa : x ∈ A
    · -- Case `x ∈ A`: use the `P1` hypothesis for `A`.
      exact hA hxa
    · -- Case `x ∉ A`: since `B ⊆ closure A`, we have `x ∈ closure A`;
      -- then use `P1_closure_subset` to pass to `closure (interior A)`.
      have hx_clA : x ∈ closure (A : Set X) := hAB₂ hxB
      have h_cl_subset :
          closure (A : Set X) ⊆ closure (interior A) :=
        Topology.P1_closure_subset (X := X) (A := A) hA
      exact h_cl_subset hx_clA
  -- Next, enlarge to `closure (interior B)` using monotonicity.
  have h_int_mono : (interior A : Set X) ⊆ interior B :=
    interior_mono hAB₁
  have h_cl_mono :
      closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int_mono
  exact h_cl_mono hx_cl_intA

theorem closure_union_nine {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I := by
  -- First, distribute `closure` over the last union.
  have h₁ :
      closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) ∪ I : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X) ∪ closure I := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X))
        (B := I)
  -- Next, apply the existing eight‐set lemma.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G ∪ closure H := by
    simpa using
      closure_union_eight (X := X)
        (A := A) (B := B) (C := C) (D := D)
        (E := E) (F := F) (G := G) (H := H)
  -- Assemble the equalities and reassociate unions.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) =
        closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) ∪ I : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H : Set X) ∪ closure I := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G ∪ closure H) ∪ closure I := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I := by
          simp [Set.union_assoc]

theorem closure_interior_left_inter_subset_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ B : Set X) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  have hx₁ : x ∈ closure (interior A) := by
    have hsubset : (interior A ∩ B : Set X) ⊆ interior A :=
      Set.inter_subset_left
    exact (closure_mono hsubset) hx
  have hx₂ : x ∈ closure B := by
    have hsubset : (interior A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact (closure_mono hsubset) hx
  exact ⟨hx₁, hx₂⟩

theorem closure_interior_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  classical
  -- We show that the intersection contains no points.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hx
  rcases hx with ⟨hxCl, hxIntCompl⟩
  -- Choose an open neighbourhood `U` of `x` contained in `Aᶜ`.
  rcases mem_interior.1 hxIntCompl with ⟨U, hUsub, hUopen, hxU⟩
  -- Because `x ∈ closure (interior A)`, the neighbourhood `U` meets `interior A`.
  have hNon : ((U : Set X) ∩ interior (A : Set X)).Nonempty := by
    have hClosure := (mem_closure_iff).1 hxCl
    -- Rearrange intersections to match Lean’s expectations.
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
      using hClosure U hUopen hxU
  -- Extract a witness `y`.
  rcases hNon with ⟨y, ⟨hyU, hyIntA⟩⟩
  -- `y ∈ A` because it lies in `interior A`.
  have hyA : y ∈ (A : Set X) := interior_subset hyIntA
  -- But `U ⊆ Aᶜ`, so `y ∈ Aᶜ`, a contradiction.
  have hyCompl : y ∈ ((A : Set X)ᶜ) := hUsub hyU
  exact hyCompl hyA

theorem P2_union_nine {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) (hF : Topology.P2 (X := X) F)
    (hG : Topology.P2 (X := X) G) (hH : Topology.P2 (X := X) H)
    (hI : Topology.P2 (X := X) I) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) := by
  -- Combine the first eight sets.
  have hABCDEFGH :
      Topology.P2 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) :=
    Topology.P2_union_eight (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) (H := H)
      hA hB hC hD hE hF hG hH
  -- Unite the result with `I`.
  have hABCDEFGHI :
      Topology.P2 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) ∪ I) :=
    Topology.P2_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) (B := I)
      hABCDEFGH hI
  -- Re‐associate the unions to match the required expression.
  simpa [Set.union_assoc] using hABCDEFGHI

theorem P3_union_nine {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) (hF : Topology.P3 (X := X) F)
    (hG : Topology.P3 (X := X) G) (hH : Topology.P3 (X := X) H)
    (hI : Topology.P3 (X := X) I) :
    Topology.P3 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) := by
  -- First, combine the properties for the first eight sets.
  have hABCDEFGH :
      Topology.P3 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) :=
    Topology.P3_union_eight (X := X)
      (A := A) (B := B) (C := C) (D := D)
      (E := E) (F := F) (G := G) (H := H)
      hA hB hC hD hE hF hG hH
  -- Unite the result with `I`.
  have hABCDEFGHI :
      Topology.P3 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) ∪ I) :=
    Topology.P3_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) (B := I)
      hABCDEFGH hI
  -- Re‐associate the unions to match the required expression.
  simpa [Set.union_assoc] using hABCDEFGHI

theorem closure_interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) ⊆ closure (A : Set X) := by
  intro x hx
  -- Step 1: `interior (closure (interior A)) ⊆ closure (interior A)`.
  have h₁ : (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
    interior_subset
  -- Hence the same inclusion holds for the closures.
  have hx_clIntA : x ∈ closure (interior A) := by
    have : x ∈ closure (closure (interior A)) :=
      (closure_mono h₁) hx
    simpa [closure_closure] using this
  -- Step 2: `closure (interior A) ⊆ closure A`.
  have h₂ : closure (interior A) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (X := X) A
  -- Combine the two steps.
  exact h₂ hx_clIntA

theorem closure_interior_union_closure_compl_interior_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∪ closure ((interior (A : Set X))ᶜ) =
      (Set.univ : Set X) := by
  simpa using
    Topology.closure_union_compl_eq_univ
      (X := X) (A := interior (A : Set X))

theorem closure_union_ten {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J := by
  -- Distribute `closure` over the last union using the two‐set lemma.
  have h₁ :
      closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) ∪ J : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) ∪ closure J := by
    simpa using
      closure_union
        (A := (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X))
        (B := J)
  -- Apply the nine‐set lemma to the first part.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G ∪ closure H ∪ closure I := by
    simpa using
      closure_union_nine (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E)
        (F := F) (G := G) (H := H) (I := I)
  -- Assemble the equalities and reassociate unions.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X)
        = closure ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) ∪ J : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I : Set X) ∪ closure J := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪
          closure E ∪ closure F ∪ closure G ∪ closure H ∪ closure I) ∪
          closure J := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J := by
          simp [Set.union_assoc]

theorem interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ⊆ closure (interior (closure A)) := by
  intro x hxIntA
  -- Step 1: `x ∈ interior (closure A)` since `A ⊆ closure A`.
  have hxIntCl : x ∈ interior (closure (A : Set X)) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxIntA
  -- Step 2: `interior (closure A) ⊆ closure (interior (closure A))`.
  have h_sub : interior (closure (A : Set X)) ⊆
      closure (interior (closure (A : Set X))) :=
    subset_closure
  -- Combine the two steps.
  exact h_sub hxIntCl

theorem closure_inter_interior_eq_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure ((A : Set X) ∩ interior A) = closure (interior A) := by
  have h : ((A : Set X) ∩ interior A) = interior A := by
    ext x
    constructor
    · intro hx; exact hx.2
    · intro hx; exact ⟨interior_subset hx, hx⟩
  simpa [h]

theorem interior_inter_interior_closure_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ interior (closure A) = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxIntA
    have hxIntCl : x ∈ interior (closure (A : Set X)) :=
      (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxIntA
    exact ⟨hxIntA, hxIntCl⟩

theorem closure_union_interior_compl_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ interior ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  classical
  -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h : interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  -- Use this equality and the fact that a set union its complement is `univ`.
  calc
    closure (A : Set X) ∪ interior ((A : Set X)ᶜ)
        = closure (A : Set X) ∪ (closure (A : Set X))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (closure (A : Set X))

theorem interior_closure_compl_eq_compl_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure ((A : Set X)ᶜ)) = (closure (interior A))ᶜ := by
  -- First, rewrite the inner `closure` using the complement–interior correspondence.
  have h₁ : closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ :=
    closure_compl_eq_compl_interior (X := X) (A := A)
  -- Substitute this equality and apply the analogous rule for `interior`.
  calc
    interior (closure ((A : Set X)ᶜ)) =
        interior ((interior (A : Set X))ᶜ) := by
          simpa [h₁]
    _ = (closure (interior (A : Set X)))ᶜ := by
          simpa using
            interior_compl_eq_compl_closure
              (X := X) (A := interior (A : Set X))

theorem interior_closure_left_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((closure (A : Set X)) ∩ B) ⊆
      interior (closure A) ∩ interior B := by
  intro x hx
  have hx₁ : x ∈ interior (closure A) :=
    (interior_mono
      (Set.inter_subset_left :
        ((closure (A : Set X)) ∩ B) ⊆ closure A)) hx
  have hx₂ : x ∈ interior B :=
    (interior_mono
      (Set.inter_subset_right :
        ((closure (A : Set X)) ∩ B) ⊆ B)) hx
  exact ⟨hx₁, hx₂⟩

theorem closureInterior_inter_interiorClosure_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : (A : Set X).Nonempty) :
    (closure (interior A) ∩ interior (closure (A : Set X))).Nonempty := by
  -- Choose a point `x` in `A`.
  rcases hA with ⟨x, hxA⟩
  -- From `P2` we obtain both `P1` and `P3`.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Hence `x` belongs to both parts of the intersection.
  have hxClInt : x ∈ closure (interior A) := hP1 hxA
  have hxIntCl : x ∈ interior (closure (A : Set X)) := hP3 hxA
  exact ⟨x, ⟨hxClInt, hxIntCl⟩⟩

theorem closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    closure (A : Set X) = Set.univ := by
  -- We establish the two inclusions separately.
  apply le_antisymm
  · -- `closure A ⊆ univ` is trivial.
    intro x _
    trivial
  · -- Show `univ ⊆ closure A`.
    intro x _
    -- Using the hypothesis, `x ∈ interior A`.
    have hxInt : x ∈ interior (A : Set X) := by
      simpa [h]
    -- `interior A ⊆ A`.
    have hxA : x ∈ (A : Set X) := interior_subset hxInt
    -- `A ⊆ closure A`.
    exact subset_closure hxA

theorem P1_union_nine {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F)
    (hG : Topology.P1 (X := X) G) (hH : Topology.P1 (X := X) H)
    (hI : Topology.P1 (X := X) I) :
    Topology.P1 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) := by
  -- Combine the properties for the first eight sets.
  have hABCDEFGH :
      Topology.P1 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) :=
    Topology.P1_union_eight (X := X)
      (A := A) (B := B) (C := C) (D := D)
      (E := E) (F := F) (G := G) (H := H)
      hA hB hC hD hE hF hG hH
  -- Unite the result with `I`.
  have hABCDEFGHI :
      Topology.P1 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) ∪ I) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H) (B := I)
      hABCDEFGH hI
  -- Re‐associate unions to match the required expression.
  simpa [Set.union_assoc] using hABCDEFGHI

theorem P3_union_ten {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) (hD : Topology.P3 (X := X) D)
    (hE : Topology.P3 (X := X) E) (hF : Topology.P3 (X := X) F)
    (hG : Topology.P3 (X := X) G) (hH : Topology.P3 (X := X) H)
    (hI : Topology.P3 (X := X) I) (hJ : Topology.P3 (X := X) J) :
    Topology.P3 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) := by
  -- Combine the properties for the first nine sets.
  have hNine :
      Topology.P3 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) :=
    Topology.P3_union_nine (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      (G := G) (H := H) (I := I)
      hA hB hC hD hE hF hG hH hI
  -- Unite the result with `J`.
  have hTen :
      Topology.P3 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) ∪ J) :=
    Topology.P3_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) (B := J)
      hNine hJ
  -- Re-associate the unions to match the required expression.
  simpa [Set.union_assoc] using hTen

theorem P2_union_ten {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) (hF : Topology.P2 (X := X) F)
    (hG : Topology.P2 (X := X) G) (hH : Topology.P2 (X := X) H)
    (hI : Topology.P2 (X := X) I) (hJ : Topology.P2 (X := X) J) :
    Topology.P2 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) := by
  -- First, combine the properties for the first nine sets.
  have hNine :
      Topology.P2 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) :=
    Topology.P2_union_nine (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      (G := G) (H := H) (I := I)
      hA hB hC hD hE hF hG hH hI
  -- Next, unite the result with `J`.
  have hTen :
      Topology.P2 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) ∪ J) :=
    Topology.P2_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) (B := J)
      hNine hJ
  -- Re‐associate the unions to match the required expression.
  simpa [Set.union_assoc] using hTen

theorem closure_interior_nonempty_of_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (interior (A : Set X)).Nonempty) :
    (closure (interior (A : Set X))).Nonempty := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, subset_closure hx⟩

theorem closureInterior_inter_interiorClosure_nonempty_of_P1_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hP3 : Topology.P3 (X := X) A)
    (hA : (A : Set X).Nonempty) :
    (closure (interior A) ∩ interior (closure (A : Set X))).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hx₁ : x ∈ closure (interior A) := hP1 hxA
  have hx₂ : x ∈ interior (closure (A : Set X)) := hP3 hxA
  exact ⟨x, ⟨hx₁, hx₂⟩⟩

theorem closure_interior_nonempty_iff_nonempty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    (closure (interior (A : Set X))).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  classical
  constructor
  · intro hCl
    by_contra hInt
    -- If `interior A` is empty, its closure is also empty,
    -- contradicting the assumed non‐emptiness.
    have hIntEmpty : interior (A : Set X) = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hInt
    have hClEmpty : closure (interior (A : Set X)) = (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty] using rfl
    have hNonemptyEmpty : (∅ : Set X).Nonempty := by
      simpa [hClEmpty] using hCl
    rcases hNonemptyEmpty with ⟨x, hx⟩
    cases hx
  · intro hInt
    exact
      Topology.closure_interior_nonempty_of_interior_nonempty
        (X := X) (A := A) hInt

theorem P1_union_ten {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F)
    (hG : Topology.P1 (X := X) G) (hH : Topology.P1 (X := X) H)
    (hI : Topology.P1 (X := X) I) (hJ : Topology.P1 (X := X) J) :
    Topology.P1 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) := by
  -- First, combine the properties for the first nine sets.
  have hNine :
      Topology.P1 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) :=
    Topology.P1_union_nine (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      (G := G) (H := H) (I := I)
      hA hB hC hD hE hF hG hH hI
  -- Unite the result with `J`.
  have hTen :
      Topology.P1 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) ∪ J) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I) (B := J)
      hNine hJ
  -- Re-associate the unions to match the required expression.
  simpa [Set.union_assoc] using hTen

theorem P2_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P2 (X := X) (closure (A : Set X)) := by
  simpa using
    Topology.isOpen_implies_P2 (X := X) (A := closure (A : Set X)) hOpen

theorem closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior ((A : Set X)ᶜ)) =
      (interior (closure (A : Set X)))ᶜ := by
  -- First, rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h₁ :
      interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  -- Substitute this equality and apply the corresponding rule for `closure`.
  calc
    closure (interior ((A : Set X)ᶜ)) =
        closure ((closure (A : Set X))ᶜ) := by
          simpa [h₁]
    _ = (interior (closure (A : Set X)))ᶜ := by
          simpa using
            closure_compl_eq_compl_interior
              (X := X) (A := closure (A : Set X))

theorem interior_eq_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    interior (A : Set X) = A := by
  simpa using hA.interior_eq

theorem interior_closure_eq_self_of_closed_and_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    interior (closure (A : Set X)) = A := by
  -- Since `A` is closed, `interior (closure A)` equals `interior A`.
  have h₁ : interior (closure (A : Set X)) = interior A :=
    interior_closure_eq_interior_of_closed (X := X) (A := A) hClosed
  -- From `hClosed` and `P3`, the set `A` is open, hence `interior A = A`.
  have hOpen : IsOpen A :=
    isOpen_of_isClosed_and_P3 (X := X) (A := A) hClosed hP3
  have h₂ : interior (A : Set X) = A := hOpen.interior_eq
  -- Combine the two equalities.
  simpa [h₁, h₂]

theorem interior_closure_interior_inter_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (A : Set X))) ∩ closure (interior A) =
      interior (closure (interior A)) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hcl : x ∈ closure (interior (A : Set X)) := interior_subset hx
    exact ⟨hx, hcl⟩

theorem closure_compl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure ((A : Set X)ᶜ) ∩ interior A = (∅ : Set X) := by
  -- Apply the existing lemma to the complement set `Aᶜ`.
  have h :=
    closure_inter_interior_compl_eq_empty (X := X) (A := (Aᶜ : Set X))
  -- Rewrite the complements to match the desired statement.
  simpa [Set.compl_compl] using h

theorem closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∩ interior (closure (A : Set X)) =
      interior (closure (A : Set X)) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxInt
    have hxCl : x ∈ closure (A : Set X) := interior_subset hxInt
    exact ⟨hxCl, hxInt⟩

theorem closureInterior_inter_interiorClosure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∩ interior (closure B) ⊆ closure (A ∩ closure B) := by
  intro x hx
  rcases hx with ⟨hxClIntA, hxIntClB⟩
  -- We prove `x ∈ closure (A ∩ closure B)` via the neighbourhood criterion.
  refine (mem_closure_iff).2 ?_
  intro U hUopen hxU
  -- Consider the open neighbourhood `V = U ∩ interior (closure B)` of `x`.
  let V : Set X := U ∩ interior (closure B)
  have hVopen : IsOpen V := hUopen.inter isOpen_interior
  have hxV : x ∈ V := ⟨hxU, hxIntClB⟩
  -- Since `x ∈ closure (interior A)`, the neighbourhood `V` meets `interior A`.
  have hNon : (V ∩ interior A).Nonempty := by
    have h := (mem_closure_iff).1 hxClIntA
    simpa [V] using h V hVopen hxV
  -- Extract a witness `y`.
  rcases hNon with ⟨y, ⟨⟨hyU, _hyIntClB⟩, hyIntA⟩⟩
  -- `y ∈ A` and `y ∈ closure B`.
  have hyA : y ∈ A := interior_subset hyIntA
  have hyClB : y ∈ closure B := interior_subset _hyIntClB
  -- `y` lies in `U ∩ (A ∩ closure B)`, hence the required non‐emptiness.
  exact ⟨y, ⟨hyU, ⟨hyA, hyClB⟩⟩⟩

theorem closure_union_eleven {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J K : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪ closure K := by
  -- First, distribute `closure` over the last union using the two-set lemma.
  have h₁ :
      closure
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) ∪ K : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X) ∪
          closure K := by
    simpa using
      closure_union
        (A :=
          (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X))
        (B := K)
  -- Apply the already-proved ten-set lemma to the first part.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J := by
    simpa using
      closure_union_ten (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
        (G := G) (H := H) (I := I) (J := J)
  -- Assemble the equalities and tidy up with associativity of `∪`.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X)
        = closure
            ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) ∪ K : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J : Set X) ∪
          closure K := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J) ∪
          closure K := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
        closure K := by
          simp [Set.union_assoc]

theorem interior_closureInterior_diff_self_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (A : Set X)) \ A) = (∅ : Set X) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    -- `x` lies in the closure of `interior A`.
    have hxClInt : x ∈ closure (interior (A : Set X)) := (hUsub hxU).1
    -- Hence every open neighbourhood of `x`, in particular `U`,
    -- meets `interior A`.
    have hNon : ((U : Set X) ∩ interior (A : Set X)).Nonempty := by
      have h := (mem_closure_iff).1 hxClInt
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        using h U hUopen hxU
    rcases hNon with ⟨y, ⟨hyU, hyIntA⟩⟩
    -- But `U` is contained in `closure (interior A) \ A`, so `y ∉ A`,
    -- contradicting `y ∈ interior A ⊆ A`.
    have hyA : y ∈ (A : Set X) := interior_subset hyIntA
    have hyNotA : y ∉ (A : Set X) := (hUsub hyU).2
    exact (hyNotA hyA).elim
  · exact Set.empty_subset _

theorem closureInterior_inter_interiorClosure_subset_closure_inter₂
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∩ interior (closure B) ⊆ closure (A ∩ closure B) := by
  intro x hx
  rcases hx with ⟨hxClIntA, hxIntClB⟩
  -- We will show `x ∈ closure (A ∩ closure B)` using `mem_closure_iff`.
  refine (mem_closure_iff).2 ?_
  intro U hUopen hxU
  -- Set `V = U ∩ interior (closure B)`, an open neighbourhood of `x`.
  let V : Set X := U ∩ interior (closure B)
  have hVopen : IsOpen V := hUopen.inter isOpen_interior
  have hxV : x ∈ V := ⟨hxU, hxIntClB⟩
  -- `x ∈ closure (interior A)` ⇒ `V` meets `interior A`.
  have hNon : (V ∩ interior A).Nonempty := by
    have h := (mem_closure_iff).1 hxClIntA
    simpa [V] using h V hVopen hxV
  -- Extract a witness `y` in `V ∩ interior A`.
  rcases hNon with ⟨y, ⟨⟨hyU, hyIntClB⟩, hyIntA⟩⟩
  -- `y ∈ A` because `y ∈ interior A`.
  have hyA : y ∈ A := interior_subset hyIntA
  -- `y ∈ closure B` because `y ∈ interior (closure B)`.
  have hyClB : y ∈ closure B := interior_subset hyIntClB
  -- Therefore `y ∈ U ∩ (A ∩ closure B)`.
  exact ⟨y, ⟨hyU, ⟨hyA, hyClB⟩⟩⟩

theorem isOpen_interior_closure_diff_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    IsOpen (interior (closure (A : Set X)) \ closure (interior A)) := by
  -- `interior (closure A)` is open, while `closure (interior A)` is closed,
  -- so their set‐difference is open.
  have h :
      IsOpen (interior (closure (A : Set X)) \ closure (interior A)) :=
    IsOpen.diff
      (X := X)
      (A := interior (closure (A : Set X)))
      (B := closure (interior A))
      isOpen_interior
      (isClosed_closure : IsClosed (closure (interior A)))
  simpa using h

theorem interior_diff_closureInterior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) \ closure (interior A) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    -- `x` lies in `interior A`.
    have hxInt : x ∈ interior (A : Set X) := hx.1
    -- `interior A ⊆ closure (interior A)`.
    have hsubset : interior (A : Set X) ⊆ closure (interior A) :=
      subset_closure
    -- Hence `x ∈ closure (interior A)`.
    have hxCl : x ∈ closure (interior A) := hsubset hxInt
    -- Contradiction with `x ∉ closure (interior A)`.
    exact (hx.2 hxCl).elim
  · intro hx
    -- No element lies in the empty set.
    cases hx

theorem interior_closure_interior_closure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior (closure A))) ⊆
      interior (closure (interior (closure B))) := by
  -- First, `closure A ⊆ closure B` by monotonicity of `closure`.
  have h₁ : closure (A : Set X) ⊆ closure B :=
    closure_mono hAB
  -- Taking `interior` on both sides yields
  -- `interior (closure A) ⊆ interior (closure B)`.
  have h₂ :
      interior (closure (A : Set X)) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Applying `closure` again preserves this inclusion.
  have h₃ :
      closure (interior (closure (A : Set X))) ⊆
        closure (interior (closure B)) :=
    closure_mono h₂
  -- Finally, taking `interior` gives the desired result.
  exact interior_mono h₃

theorem P1_union_eleven {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J K : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F)
    (hG : Topology.P1 (X := X) G) (hH : Topology.P1 (X := X) H)
    (hI : Topology.P1 (X := X) I) (hJ : Topology.P1 (X := X) J)
    (hK : Topology.P1 (X := X) K) :
    Topology.P1 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) := by
  -- First, combine the properties for the first ten sets.
  have hTen :
      Topology.P1 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) :=
    Topology.P1_union_ten (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      (G := G) (H := H) (I := I) (J := J)
      hA hB hC hD hE hF hG hH hI hJ
  -- Unite the result with `K`.
  have hEleven :
      Topology.P1 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) ∪ K) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) (B := K)
      hTen hK
  -- Re‐associate unions to match the desired expression.
  simpa [Set.union_assoc] using hEleven

theorem closure_eq_closure_interior_union_closure_diff
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) =
      closure (interior A) ∪ closure (A \ interior A) := by
  classical
  ext x
  constructor
  · intro hxClA
    by_cases hClInt : x ∈ closure (interior A)
    · exact Or.inl hClInt
    · -- Put `x` in the complement of `closure (interior A)`.
      have hxW : x ∈ (closure (interior (A : Set X)))ᶜ := by
        simpa [Set.mem_compl] using hClInt
      -- Show `x ∈ closure (A \ interior A)`.
      have hxClDiff : x ∈ closure (A \ interior A : Set X) := by
        -- Use the neighbourhood characterisation of the closure.
        refine (mem_closure_iff).2 ?_
        intro U hUopen hxU
        -- Intersect with the open set `W` that avoids `interior A`.
        let W : Set X := (closure (interior (A : Set X)))ᶜ
        have hWopen : IsOpen W := isClosed_closure.isOpen_compl
        have hxW' : x ∈ W := hxW
        let V : Set X := U ∩ W
        have hVopen : IsOpen V := hUopen.inter hWopen
        have hxV : x ∈ V := by
          exact And.intro hxU hxW'
        -- Since `x ∈ closure A`, `V` meets `A`.
        have hNon : ((V : Set X) ∩ (A : Set X)).Nonempty := by
          have := (mem_closure_iff).1 hxClA V hVopen hxV
          simpa [V, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
        -- Extract a point `y` in `V ∩ A`; it cannot lie in `interior A`.
        rcases hNon with ⟨y, ⟨⟨hyU, hyW⟩, hyA⟩⟩
        have hyNotInt : y ∈ (interior (A : Set X))ᶜ := by
          intro hyInt
          have : y ∈ closure (interior (A : Set X)) := subset_closure hyInt
          exact hyW this
        have hyDiff : y ∈ A \ interior A := ⟨hyA, hyNotInt⟩
        exact ⟨y, ⟨hyU, hyDiff⟩⟩
      exact Or.inr hxClDiff
  · intro hx
    cases hx with
    | inl hxInt =>
        have hsubset : closure (interior A) ⊆ closure (A : Set X) :=
          Topology.closure_interior_subset_closure (X := X) A
        exact hsubset hxInt
    | inr hxDiff =>
        have hsubset :
            closure (A \ interior A : Set X) ⊆ closure (A : Set X) :=
          closure_mono (Set.diff_subset : (A \ interior A : Set X) ⊆ A)
        exact hsubset hxDiff

theorem closure_union_twelve {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J K L : Set X} :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K ∪ L : Set X) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
        closure K ∪ closure L := by
  -- First, distribute `closure` over the final union with `L`.
  have h₁ :
      closure
          ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) ∪ L : Set X) =
        closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X) ∪
          closure L := by
    simpa using
      closure_union
        (A :=
          (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X))
        (B := L)
  -- Next, apply the existing eleven‐set lemma to the first term.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
          closure K := by
    simpa using
      closure_union_eleven (X := X)
        (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
        (G := G) (H := H) (I := I) (J := J) (K := K)
  -- Combine the equalities and tidy up with associativity of `∪`.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K ∪ L : Set X)
        = closure
            ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) ∪ L : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K : Set X) ∪
          closure L := by
          simpa using h₁
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
          closure K) ∪ closure L := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
        closure F ∪ closure G ∪ closure H ∪ closure I ∪ closure J ∪
        closure K ∪ closure L := by
          simp [Set.union_assoc]

theorem P1_union_twelve {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J K L : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D)
    (hE : Topology.P1 (X := X) E) (hF : Topology.P1 (X := X) F)
    (hG : Topology.P1 (X := X) G) (hH : Topology.P1 (X := X) H)
    (hI : Topology.P1 (X := X) I) (hJ : Topology.P1 (X := X) J)
    (hK : Topology.P1 (X := X) K) (hL : Topology.P1 (X := X) L) :
    Topology.P1 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K ∪ L) := by
  -- Combine the first eleven sets using the existing lemma.
  have hEleven :
      Topology.P1 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) :=
    Topology.P1_union_eleven (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      (G := G) (H := H) (I := I) (J := J) (K := K)
      hA hB hC hD hE hF hG hH hI hJ hK
  -- Unite the result with `L`.
  have hTwelve :
      Topology.P1 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) ∪ L) :=
    Topology.P1_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) (B := L)
      hEleven hL
  -- Reassociating unions to match the desired shape.
  simpa [Set.union_assoc] using hTwelve

theorem interior_closure_iterate_from_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure S)) (n.succ) (interior A) =
      interior (closure (interior A)) := by
  -- Define `f := interior ∘ closure`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.interior_closure_idempotent (X := X) (A := S)
  -- A helper lemma: iterating an idempotent function on a fixed point
  -- leaves the point unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewriting the iterate so that it starts from the fixed point `f (interior A)`.
  have h_step :
      Nat.iterate f (n.succ) (interior A) =
        Nat.iterate f n (f (interior A)) := by
    simp [Nat.iterate]
  -- Since `f (interior A)` is a fixed point, the right‐hand side collapses.
  have h_iter :
      Nat.iterate f n (f (interior A)) = f (interior A) := by
    have hfix : f (f (interior A)) = f (interior A) := by
      simpa using hf_id (interior A)
    exact iterate_fixed hfix n
  -- Assemble the equalities and unfold `f`.
  simpa [f, h_step, h_iter]

theorem interior_closure_interior_left_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior (A : Set X) ∩ B)) ⊆
      interior (closure (interior A)) ∩ interior (closure B) := by
  simpa using
    interior_closure_inter_subset (X := X) (A := interior A) (B := B)

theorem closureInterior_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxClIntA, hxIntB⟩
  -- We will show `x ∈ closure (A ∩ B)` using the neighbourhood criterion.
  have : x ∈ closure (A ∩ B : Set X) := by
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighbourhood `V = U ∩ interior B` of `x`.
    have hVopen : IsOpen (U ∩ interior B) := hUopen.inter isOpen_interior
    have hxV : x ∈ U ∩ interior B := ⟨hxU, hxIntB⟩
    -- Since `x ∈ closure (interior A)`, this neighbourhood meets `interior A`.
    have hNon : ((U ∩ interior B : Set X) ∩ interior A).Nonempty := by
      have h := (mem_closure_iff).1 hxClIntA
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        using h (U ∩ interior B) hVopen hxV
    -- Extract a point `y` in the intersection.
    rcases hNon with ⟨y, ⟨⟨hyU, hyIntB⟩, hyIntA⟩⟩
    have hyA : y ∈ A := interior_subset hyIntA
    have hyB : y ∈ B := interior_subset hyIntB
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this

theorem interior_closure_union_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B : Set X)) = interior (closure A ∪ closure B) := by
  simpa using
    congrArg interior
      (closure_union (A := (A : Set X)) (B := B))

theorem closure_inter_interior_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A : Set X)) ∩ interior A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxInt
    have hxCl : x ∈ closure (interior (A : Set X)) := subset_closure hxInt
    exact ⟨hxCl, hxInt⟩

theorem subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A) :
    (A : Set X) ⊆ closure (interior A) := by
  intro x hx
  exact hP1 hx

theorem closure_interior_inter_closure_interior_eq_left_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ∩ closure (interior B) = closure (interior A) := by
  -- `interior` is monotone, hence so is `closure ∘ interior`.
  have hsubset : closure (interior (A : Set X)) ⊆ closure (interior B) := by
    have h₁ : (interior (A : Set X) : Set X) ⊆ interior B :=
      interior_mono hAB
    exact closure_mono h₁
  -- Establish the desired set equality via double inclusion.
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxA
    exact ⟨hxA, hsubset hxA⟩

theorem P2_union_eleven {X : Type*} [TopologicalSpace X]
    {A B C D E F G H I J K : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D)
    (hE : Topology.P2 (X := X) E) (hF : Topology.P2 (X := X) F)
    (hG : Topology.P2 (X := X) G) (hH : Topology.P2 (X := X) H)
    (hI : Topology.P2 (X := X) I) (hJ : Topology.P2 (X := X) J)
    (hK : Topology.P2 (X := X) K) :
    Topology.P2 (X := X)
      (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J ∪ K) := by
  -- Combine the first ten sets using the existing `P2_union_ten`.
  have hTen :
      Topology.P2 (X := X)
        (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) :=
    Topology.P2_union_ten (X := X)
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F)
      (G := G) (H := H) (I := I) (J := J)
      hA hB hC hD hE hF hG hH hI hJ
  -- Unite the result with `K`.
  have hEleven :
      Topology.P2 (X := X)
        ((A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) ∪ K) :=
    Topology.P2_union (X := X)
      (A := A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G ∪ H ∪ I ∪ J) (B := K)
      hTen hK
  -- Re-associate the unions to match the desired expression.
  simpa [Set.union_assoc] using hEleven

theorem closure_inter_closure_compl_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∩ closure ((A : Set X)ᶜ) =
      closure (A : Set X) \ interior A := by
  classical
  -- Rewrite the closure of the complement via the interior.
  have h :
      closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ :=
    closure_compl_eq_compl_interior (X := X) (A := A)
  -- Substitute this equality and use the definition of set difference.
  calc
    closure (A : Set X) ∩ closure ((A : Set X)ᶜ)
        = closure (A : Set X) ∩ (interior (A : Set X))ᶜ := by
          simpa [h]
    _ = closure (A : Set X) \ interior A := by
          simpa [Set.diff_eq, Set.inter_comm]

theorem closure_inter_closure_compl_of_closureInterior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∩ closure ((interior (A : Set X))ᶜ) =
      closure (interior (A : Set X)) \ interior A := by
  simpa [interior_interior] using
    (closure_inter_closure_compl_eq_closure_diff_interior
      (X := X) (A := interior (A : Set X)))