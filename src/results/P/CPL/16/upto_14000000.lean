import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

def P1 (A : Set X) : Prop :=
  A ⊆ closure (interior A)

def P2 (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

def P3 (A : Set X) : Prop :=
  A ⊆ interior (closure A)


theorem P2_subset_P1 (A : Set X) : P2 A → P1 A := by
  intro h
  exact h.trans interior_subset

theorem P2_imp_P3 (A : Set X) : P2 A → P3 A := by
  intro h
  exact h.trans (interior_mono (closure_mono interior_subset))

theorem P1_union_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  have hA' : (A : Set X) ⊆ closure (interior (A ∪ B)) :=
    hA.trans (closure_mono (interior_mono Set.subset_union_left))
  have hB' : (B : Set X) ⊆ closure (interior (A ∪ B)) :=
    hB.trans (closure_mono (interior_mono Set.subset_union_right))
  exact Set.union_subset hA' hB'

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  unfold P1
  intro x hx
  cases hx

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  unfold P1
  simpa [interior_univ, closure_univ]

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  unfold P2
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  unfold P3
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  unfold P2
  intro x hx
  have : x ∈ interior (closure (interior A)) :=
    (interior_mono (subset_closure)) (by
      simpa [interior_interior] using hx)
  simpa [interior_interior] using this

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hA hB
  unfold P2 at hA hB ⊢
  exact
    Set.union_subset
      (hA.trans <|
        interior_mono <| closure_mono <| interior_mono Set.subset_union_left)
      (hB.trans <|
        interior_mono <| closure_mono <| interior_mono Set.subset_union_right)

theorem P3_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hA
  exact interior_maximal subset_closure hA

theorem exists_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P2 B := by
  exact ⟨(∅ : Set X), Set.empty_subset _, P2_empty⟩

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P3 A) → P3 (⋃₀ 𝒜) := by
  intro hP3
  classical
  refine Set.sUnion_subset ?_
  intro A hA
  have hPA : P3 A := hP3 A hA
  have h1 : (A : Set X) ⊆ interior (closure A) := hPA
  have h2 : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono (closure_mono (Set.subset_sUnion_of_mem hA))
  exact h1.trans h2

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  unfold P3 at hA hB ⊢
  exact
    Set.union_subset
      (hA.trans <| interior_mono <| closure_mono Set.subset_union_left)
      (hB.trans <| interior_mono <| closure_mono Set.subset_union_right)

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P1 A) → P1 (⋃₀ 𝒜) := by
  intro hP1
  classical
  refine Set.sUnion_subset ?_
  intro A hA
  have hPA : P1 A := hP1 A hA
  have h1 : (A : Set X) ⊆ closure (interior A) := hPA
  have h2 : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono (interior_mono (Set.subset_sUnion_of_mem hA))
  exact h1.trans h2

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P2 A) → P2 (⋃₀ 𝒜) := by
  intro hP2
  unfold P2 at hP2 ⊢
  refine Set.sUnion_subset ?_
  intro B hB
  have hPB : (B : Set X) ⊆ interior (closure (interior B)) := hP2 B hB
  have h2 :
      interior (closure (interior B)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono <| closure_mono <| interior_mono <| Set.subset_sUnion_of_mem hB
  exact hPB.trans h2

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  simpa [P1, interior_interior] using
    (subset_closure : (interior A : Set X) ⊆ closure (interior A))

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  exact (P2_imp_P3 (interior A)) P2_interior

theorem exists_P3_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P3 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  have h : P3 (∅ : Set X) := (P2_imp_P3 (∅ : Set X)) P2_empty
  simpa using h

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  unfold P1 at hP1 ⊢
  intro x hx
  -- show that every neighborhood of `x` meets `interior (closure A)`
  apply (mem_closure_iff).2
  intro U hU hxU
  -- since `x ∈ closure A`, `U` meets `A`
  have hUA : (U ∩ A).Nonempty := by
    have := (mem_closure_iff).1 hx U hU hxU
    simpa using this
  rcases hUA with ⟨y, hyU, hyA⟩
  -- from `P1 A` we know `y ∈ closure (interior A)`
  have hy_clos : y ∈ closure (interior A) := hP1 hyA
  -- hence `U` meets `interior A`
  have hU_intA : (U ∩ interior A).Nonempty := by
    have := (mem_closure_iff).1 hy_clos U hU hyU
    simpa using this
  rcases hU_intA with ⟨z, hzU, hzIntA⟩
  -- but `interior A ⊆ interior (closure A)`
  have hzIntClA : z ∈ interior (closure A) :=
    (interior_mono subset_closure) hzIntA
  exact ⟨z, hzU, hzIntClA⟩

theorem exists_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P1 B := by
  exact ⟨(∅ : Set X), Set.empty_subset _, P1_empty⟩

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  unfold P3
  intro x hx
  cases hx

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} : (∀ i, P2 (f i)) → P2 (⋃ i, f i) := by
  intro hP2
  -- unfold definitions
  unfold P2 at hP2 ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx' : x ∈ interior (closure (interior (f i))) := hP2 i hxi
  have hsubset :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ j, f j))) :=
    interior_mono <|
      closure_mono <|
        interior_mono <|
          Set.subset_iUnion (fun j : ι => f j) i
  exact hsubset hx'

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro hDense
  intro x hx
  simpa [hDense, interior_univ]

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} : (∀ i, P3 (f i)) → P3 (⋃ i, f i) := by
  intro hP3
  unfold P3 at hP3 ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx' : x ∈ interior (closure (f i)) := hP3 i hxi
  have hsubset :
      interior (closure (f i)) ⊆ interior (closure (⋃ j, f j)) :=
    interior_mono <| closure_mono <| Set.subset_iUnion (fun j => f j) i
  exact hsubset hx'

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA
  unfold P2
  intro x hx
  have hx' : x ∈ interior (closure A) := (P3_open hA) hx
  simpa [hA.interior_eq] using hx'

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  simpa [P2, interior_univ, closure_univ]

theorem P1_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hA
  unfold P1
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem exists_P2_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ P2 B := by
  refine ⟨Set.univ, ?_, P2_univ⟩
  intro x hx
  trivial

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} : (∀ i, P1 (f i)) → P1 (⋃ i, f i) := by
  intro hP1
  unfold P1 at hP1 ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx' : x ∈ closure (interior (f i)) := hP1 i hxi
  have hsubset :
      closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) :=
    closure_mono <| interior_mono <| Set.subset_iUnion (fun j : ι => f j) i
  exact hsubset hx'

theorem exists_P2_closed_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ IsClosed B ∧ P2 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, isClosed_empty, P2_empty⟩

theorem exists_P1_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ IsOpen B ∧ P1 B := by
  refine ⟨Set.univ, ?_, isOpen_univ, P1_univ⟩
  intro x hx
  trivial

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · simpa [hA] using (P1_empty : P1 (∅ : Set X))
  · -- `A` is nonempty, hence equal to `univ`
    have hne : (A : Set X).Nonempty := Set.nonempty_iff_ne_empty.2 hA
    rcases hne with ⟨x, hx⟩
    have hAu : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; simp
      · intro _; 
        have : y = x := Subsingleton.elim y x
        simpa [this] using hx
    simpa [hAu] using (P1_univ : P1 (Set.univ : Set X))

theorem exists_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ P3 B := by
  refine ⟨Set.univ, ?_, P3_univ⟩
  intro x hx
  trivial

theorem exists_P1_closed_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ IsClosed B ∧ P1 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, isClosed_empty, P1_empty⟩

theorem exists_P2_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ IsOpen B ∧ P2 B := by
  refine ⟨Set.univ, ?_, isOpen_univ, P2_univ⟩
  intro x hx
  trivial

theorem P1_eq_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P1 A → closure (interior A) = A := by
  intro hClosed hP1
  exact
    Set.Subset.antisymm
      (closure_minimal interior_subset hClosed)
      hP1

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P2 A := by
  simpa [P3, P2, hA.interior_eq]

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · simpa [hA] using (P2_empty : P2 (∅ : Set X))
  · -- `A` is nonempty, hence equal to `univ`
    have hne : (A : Set X).Nonempty := Set.nonempty_iff_ne_empty.2 hA
    rcases hne with ⟨x, hx⟩
    have hAu : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; trivial
      · intro _
        have hxy : y = x := Subsingleton.elim y x
        simpa [hxy] using hx
    simpa [hAu] using (P2_univ : P2 (Set.univ : Set X))

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  exact (P2_imp_P3 A) P2_subsingleton

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → P1 A := by
  intro hClosed hP3
  intro x hxA
  have hxIntClosure : x ∈ interior (closure A) := hP3 hxA
  have hClosureEq : closure A = A := hClosed.closure_eq
  have hxInt : x ∈ interior A := by
    simpa [hClosureEq] using hxIntClosure
  exact subset_closure hxInt

theorem P1_iff_P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → (P1 A ↔ P2 A) := by
  intro hDense
  constructor
  · intro hP1
    -- First, show that `closure (interior A) = univ`.
    have h_subset : (closure (A : Set X)) ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure (interior A) := hP1
      exact closure_minimal hA isClosed_closure
    have h_univ : (Set.univ : Set X) ⊆ closure (interior A) := by
      simpa [hDense] using h_subset
    have h_closure_int_univ : closure (interior A) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · exact h_univ
    -- With this equality, `P2 A` follows.
    have hP2 : P2 A := by
      intro x hxA
      have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [h_closure_int_univ, interior_univ] using hx_univ
    exact hP2
  · intro hP2
    exact (P2_subset_P1 (A := A)) hP2

theorem exists_P1_closed_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B, A ⊆ B ∧ IsClosed B ∧ P1 B := by
  refine ⟨Set.univ, ?_, isClosed_univ, P1_univ⟩
  intro x hx
  trivial

theorem exists_P2_closed_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ IsClosed B ∧ P2 B := by
  refine ⟨Set.univ, ?_, isClosed_univ, P2_univ⟩
  intro x hx
  trivial

theorem P2_iff_P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact (P2_subset_P1 (A := A)) hP2
  · intro _hP1
    exact P2_of_open hA

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → P1 A := by
  intro hInt
  -- Since `interior A = univ`, its closure is also `univ`.
  have h_closure : (closure (interior A) : Set X) = Set.univ := by
    simpa [hInt, closure_univ]
  -- Provide the required inclusion.
  have h_subset : (A : Set X) ⊆ closure (interior A) := by
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [h_closure] using this
  simpa [P1] using h_subset

theorem exists_P3_closed_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ IsClosed B ∧ P3 B := by
  refine ⟨Set.univ, ?_, isClosed_univ, P3_univ⟩
  intro x hx
  trivial

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∩ B) := by
  intro hA hB
  -- unfold the definition of `P2`
  unfold P2 at hA hB ⊢
  intro x hx
  -- split the membership of `x`
  have hxA : x ∈ A := hx.1
  have hxB : x ∈ B := hx.2
  -- the two regular–open supersets coming from the hypotheses
  have hx_rA : x ∈ interior (closure (interior A)) := hA hxA
  have hx_rB : x ∈ interior (closure (interior B)) := hB hxB
  -- define the open set `U`
  let U : Set X := interior (closure (interior A)) ∩ interior (closure (interior B))
  have hU_open : IsOpen (U : Set X) := (isOpen_interior).inter isOpen_interior
  have hxU : x ∈ (U : Set X) := by
    dsimp [U] at *
    exact ⟨hx_rA, hx_rB⟩
  -- show `U ⊆ closure (interior (A ∩ B))`
  have hUsubset : (U : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro z hz
    have hz_rA : z ∈ interior (closure (interior A)) := hz.1
    have hz_rB : z ∈ interior (closure (interior B)) := hz.2
    -- neighbourhood characterization of the closure
    apply (mem_closure_iff).2
    intro V hV hzV
    -- Step 1 : meet `interior A`
    have h_open₁ : IsOpen (V ∩ interior (closure (interior B))) :=
      hV.inter isOpen_interior
    have hz_open₁ : z ∈ V ∩ interior (closure (interior B)) := ⟨hzV, hz_rB⟩
    have hz_clA : z ∈ closure (interior A) := (interior_subset) hz_rA
    have h_nonempty₁ :
        ((V ∩ interior (closure (interior B))) ∩ interior A).Nonempty := by
      have h := (mem_closure_iff).1 hz_clA _ h_open₁ hz_open₁
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
    rcases h_nonempty₁ with ⟨w₁, ⟨⟨hw₁V, hw₁_rB⟩, hw₁_intA⟩⟩
    -- Step 2 : meet `interior B`
    have hw₁_clB : w₁ ∈ closure (interior B) := (interior_subset) hw₁_rB
    have h_open₂ : IsOpen (V ∩ interior A) := hV.inter isOpen_interior
    have hw₁_open₂ : w₁ ∈ V ∩ interior A := ⟨hw₁V, hw₁_intA⟩
    have h_nonempty₂ : ((V ∩ interior A) ∩ interior B).Nonempty := by
      have h := (mem_closure_iff).1 hw₁_clB _ h_open₂ hw₁_open₂
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
    rcases h_nonempty₂ with ⟨w, ⟨⟨hwV, hw_intA⟩, hw_intB⟩⟩
    -- `w` belongs to `interior (A ∩ B)`
    have hw_intAB : w ∈ interior (A ∩ B) := by
      -- an open neighbourhood contained in `A ∩ B`
      have hOpen : IsOpen (interior A ∩ interior B) :=
        (isOpen_interior).inter isOpen_interior
      have hSub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
        intro t ht
        exact ⟨(interior_subset) ht.1, (interior_subset) ht.2⟩
      have hIncl := interior_maximal hSub hOpen
      exact hIncl ⟨hw_intA, hw_intB⟩
    exact ⟨w, hwV, hw_intAB⟩
  -- `x` lies in the open set `U`, which is contained in the desired set
  have : x ∈ interior (closure (interior (A ∩ B))) := by
    have hIncl := interior_maximal hUsubset hU_open
    exact hIncl hxU
  exact this

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    · -- `closure (interior A)` is contained in `closure A`
      exact closure_mono interior_subset
    · -- `closure A` is contained in `closure (interior A)` since `A ⊆ closure (interior A)`
      exact closure_minimal hP1 isClosed_closure
  · intro hEq
    -- rewrite `subset_closure` using the given equality
    have h : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq.symm] using h

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → P2 A := by
  intro hInt
  intro x hx
  have hEq : (interior (closure (interior A)) : Set X) = Set.univ := by
    simpa [hInt, closure_univ, interior_univ]
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hEq] using hx_univ

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} : IsClosed B → P2 A → P2 (A \ B) := by
  intro hB hP2A
  -- unfold the definition of `P2`
  unfold P2 at hP2A ⊢
  intro x hx
  -- split the hypothesis `x ∈ A \ B`
  have hxA : x ∈ A := hx.1
  have hxNotB : x ∈ (Bᶜ : Set X) := hx.2
  -- from `P2 A`, obtain that `x` belongs to the open set
  have hxIntA : x ∈ interior (closure (interior A)) := hP2A hxA
  -- define the auxiliary open neighbourhood `U`
  set U : Set X := interior (closure (interior A)) ∩ Bᶜ with hUdef
  have hOpenU : IsOpen U := by
    simpa [hUdef] using (isOpen_interior).inter hB.isOpen_compl
  have hxU : x ∈ U := by
    simpa [hUdef] using And.intro hxIntA hxNotB
  -- show `U ⊆ closure (interior (A \ B))`
  have hUsubset : (U : Set X) ⊆ closure (interior (A \ B)) := by
    intro z hz
    rcases (show z ∈ U from hz) with ⟨hzIntA, hzNotB⟩
    -- `z` belongs to the closure of `interior A`
    have hzClIntA : z ∈ closure (interior A) := interior_subset hzIntA
    -- show that `z` is in the closure of `interior (A \ B)`
    have : z ∈ closure (interior (A \ B)) := by
      -- use the characterization of closure via neighbourhoods
      apply (mem_closure_iff).2
      intro W hW hzW
      -- consider the open set `W ∩ Bᶜ`
      have hOpen : IsOpen (W ∩ Bᶜ : Set X) := hW.inter hB.isOpen_compl
      have hzIn : z ∈ W ∩ Bᶜ := ⟨hzW, hzNotB⟩
      -- since `z ∈ closure (interior A)`, this intersection meets `interior A`
      have hNonempty :
          ((W ∩ Bᶜ) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hzClIntA _ hOpen hzIn
      rcases hNonempty with ⟨y, ⟨⟨hyW, hyNotB⟩, hyIntA⟩⟩
      -- `y` lies in `W`, in `interior A`, and outside `B`
      -- show that `y ∈ interior (A \ B)`
      have hyIntDiff : y ∈ interior (A \ B) := by
        -- open set contained in `A \ B`
        have hOpen' : IsOpen ((interior A) ∩ Bᶜ : Set X) :=
          (isOpen_interior).inter hB.isOpen_compl
        have hSub' : ((interior A) ∩ Bᶜ : Set X) ⊆ A \ B := by
          intro t ht
          exact ⟨(interior_subset) ht.1, ht.2⟩
        have hIncl := interior_maximal hSub' hOpen'
        exact hIncl ⟨hyIntA, hyNotB⟩
      -- hence, `W` meets `interior (A \ B)`
      exact ⟨y, ⟨hyW, hyIntDiff⟩⟩
    exact this
  -- `x` lies in the open set `U`, which is contained in the desired set
  have hInt := interior_maximal hUsubset hOpenU
  exact hInt hxU

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen (closure A) → P3 A := by
  intro hOpen
  intro x hx
  have hx' : (x : X) ∈ closure A := subset_closure hx
  simpa [hOpen.interior_eq] using hx'

theorem P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → (P2 A ↔ P3 A) := by
  intro hInt
  constructor
  · intro hP2
    exact (P2_imp_P3 (A := A)) hP2
  · intro _hP3
    exact (P2_of_dense_interior (A := A)) hInt

theorem P1_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} : IsClosed B → P1 A → P1 (A \ B) := by
  intro hB hP1
  -- we prove that every point of `A \ B` belongs to the closure of `interior (A \ B)`
  unfold P1 at hP1 ⊢
  intro x hxDiff
  -- from `P1 A`
  have hCl : x ∈ closure (interior A) := hP1 hxDiff.1
  -- use the neighbourhood characterization of the closure
  apply (mem_closure_iff).2
  intro U hU hxU
  -- refine the neighbourhood so that it is disjoint from `B`
  have hVopen : IsOpen (U ∩ (Bᶜ) : Set X) := hU.inter hB.isOpen_compl
  have hxV : x ∈ (U ∩ (Bᶜ) : Set X) := by
    refine ⟨hxU, hxDiff.2⟩
  -- since `x` is in the closure of `interior A`, the refined neighbourhood
  -- meets `interior A`
  have hNonempty : ((U ∩ (Bᶜ)) ∩ interior A).Nonempty := by
    have := (mem_closure_iff).1 hCl _ hVopen hxV
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
  rcases hNonempty with ⟨y, ⟨⟨hyU, hyNotB⟩, hyIntA⟩⟩
  -- the point `y` is in `interior A` and outside `B`; hence it belongs to
  -- `interior (A \ B)`
  have hyIntDiff : y ∈ interior (A \ B) := by
    -- the open set `interior A ∩ Bᶜ` is contained in `A \ B`
    have hOpen : IsOpen ((interior A) ∩ (Bᶜ) : Set X) :=
      (isOpen_interior).inter hB.isOpen_compl
    have hSub : ((interior A) ∩ (Bᶜ) : Set X) ⊆ A \ B := by
      intro z hz
      rcases hz with ⟨hzIntA, hzNotB⟩
      exact ⟨(interior_subset) hzIntA, hzNotB⟩
    have hIncl := interior_maximal hSub hOpen
    exact hIncl ⟨hyIntA, hyNotB⟩
  -- `y` is the required point in `U ∩ interior (A \ B)`
  exact ⟨y, hyU, hyIntDiff⟩

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P3 A := by
  have h1 : P1 A ↔ P2 A := (P2_iff_P1_of_open (A := A) hA).symm
  have h2 : P2 A ↔ P3 A := (P3_iff_P2_of_open (A := A) hA).symm
  exact h1.trans h2

theorem exists_P1_dense_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, A ⊆ U ∧ IsOpen U ∧ closure U = Set.univ ∧ P1 U := by
  refine ⟨Set.univ, ?_, isOpen_univ, closure_univ, P1_univ⟩
  intro x hx
  trivial

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (Set.prod A B) := by
  intro hA hB
  -- unpack the definitions
  unfold P1 at hA hB ⊢
  intro p hp
  -- split the point and the hypothesis
  rcases p with ⟨x, y⟩
  -- `hp` states that `(x, y)` belongs to `A ×ˢ B`
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- put the two coordinates in the appropriate closures
  have hx_cl : x ∈ closure (interior A) := hA hxA
  have hy_cl : y ∈ closure (interior B) := hB hyB
  -- we show that `(x, y)` is in `closure (interior (A ×ˢ B))`
  apply (mem_closure_iff).2
  intro W hW hWxy
  -- work with a basic neighbourhood of `(x, y)`
  have hW_nhds : (W : Set (X × Y)) ∈ nhds (x, y) := IsOpen.mem_nhds hW hWxy
  rcases (mem_nhds_prod_iff).1 hW_nhds with ⟨U, hU_nhds, V, hV_nhds, hUV_sub⟩
  -- choose open subsets of `U` and `V`
  rcases (mem_nhds_iff).1 hU_nhds with ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
  rcases (mem_nhds_iff).1 hV_nhds with ⟨V₀, hV₀_sub, hV₀_open, hyV₀⟩
  -- `U₀` meets `interior A`
  have hA_nonempty : ((U₀ ∩ interior A) : Set X).Nonempty := by
    have := (mem_closure_iff).1 hx_cl U₀ hU₀_open hxU₀
    simpa [Set.inter_comm] using this
  rcases hA_nonempty with ⟨a', ha'⟩
  have ha'U₀   : a' ∈ U₀           := ha'.1
  have ha'intA : a' ∈ interior A  := ha'.2
  -- `V₀` meets `interior B`
  have hB_nonempty : ((V₀ ∩ interior B) : Set Y).Nonempty := by
    have := (mem_closure_iff).1 hy_cl V₀ hV₀_open hyV₀
    simpa [Set.inter_comm] using this
  rcases hB_nonempty with ⟨b', hb'⟩
  have hb'V₀   : b' ∈ V₀           := hb'.1
  have hb'intB : b' ∈ interior B  := hb'.2
  -- the pair `(a', b')` lies in `W`
  have h_pair_W : (a', b') ∈ W := by
    have : (a', b') ∈ Set.prod U V := by
      exact ⟨hU₀_sub ha'U₀, hV₀_sub hb'V₀⟩
    exact hUV_sub this
  -- the pair `(a', b')` lies in `interior (A ×ˢ B)`
  have h_pair_int : (a', b') ∈ interior (Set.prod A B) := by
    -- open set `S = interior A ×ˢ interior B`
    let S : Set (X × Y) := Set.prod (interior A) (interior B)
    have hS_open   : IsOpen S := (isOpen_interior).prod isOpen_interior
    have hS_subset : (S : Set (X × Y)) ⊆ Set.prod A B := by
      intro q hq
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨interior_subset hqA, interior_subset hqB⟩
    have hInS : (a', b') ∈ S := by
      exact ⟨ha'intA, hb'intB⟩
    -- since `S` is open, its interior is itself
    have hIn_int_S : (a', b') ∈ interior S := by
      simpa [hS_open.interior_eq] using hInS
    -- use monotonicity of `interior`
    exact (interior_mono hS_subset) hIn_int_S
  -- conclude
  exact ⟨(a', b'), h_pair_W, h_pair_int⟩

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (Set.prod A B) := by
  intro hA hB
  -- unfold the definition of `P2`
  unfold P2 at hA hB ⊢
  intro p hp
  -- split the point and the hypothesis
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- put the two coordinates inside the relevant open sets
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  have hy_int : y ∈ interior (closure (interior B)) := hB hyB
  -- define the auxiliary open neighbourhood `U`
  let U : Set (X × Y) :=
    Set.prod (interior (closure (interior A))) (interior (closure (interior B)))
  have hU_open : IsOpen (U : Set (X × Y)) :=
    (isOpen_interior).prod isOpen_interior
  have hpU : (x, y) ∈ U := by
    dsimp [U]
    exact ⟨hx_int, hy_int⟩
  -- show `U ⊆ closure (interior (A ×ˢ B))`
  have hU_sub : (U : Set (X × Y)) ⊆ closure (interior (Set.prod A B)) := by
    intro z hz
    rcases z with ⟨a, b⟩
    dsimp [U] at hz
    rcases hz with ⟨ha_intA, hb_intB⟩
    -- move to the closure of the interiors
    have ha_clA : a ∈ closure (interior A) := interior_subset ha_intA
    have hb_clB : b ∈ closure (interior B) := interior_subset hb_intB
    -- characterize membership in the closure
    apply (mem_closure_iff).2
    intro W hW hWab
    -- use a rectangular neighbourhood of `(a, b)`
    have hW_nhds : (W : Set (X × Y)) ∈ nhds (a, b) := IsOpen.mem_nhds hW hWab
    rcases (mem_nhds_prod_iff).1 hW_nhds with
      ⟨U', hU'_nhds, V', hV'_nhds, hUV'_sub⟩
    rcases (mem_nhds_iff).1 hU'_nhds with
      ⟨U₀, hU₀_sub, hU₀_open, haU₀⟩
    rcases (mem_nhds_iff).1 hV'_nhds with
      ⟨V₀, hV₀_sub, hV₀_open, hbV₀⟩
    -- `U₀` meets `interior A`
    have hA_nonempty : ((U₀ ∩ interior A) : Set X).Nonempty := by
      have := (mem_closure_iff).1 ha_clA U₀ hU₀_open haU₀
      simpa [Set.inter_comm] using this
    rcases hA_nonempty with ⟨a', ha'⟩
    have ha'U₀   : a' ∈ U₀          := ha'.1
    have ha'intA : a' ∈ interior A := ha'.2
    -- `V₀` meets `interior B`
    have hB_nonempty : ((V₀ ∩ interior B) : Set Y).Nonempty := by
      have := (mem_closure_iff).1 hb_clB V₀ hV₀_open hbV₀
      simpa [Set.inter_comm] using this
    rcases hB_nonempty with ⟨b', hb'⟩
    have hb'V₀   : b' ∈ V₀          := hb'.1
    have hb'intB : b' ∈ interior B := hb'.2
    -- the pair `(a', b')` lies in `W`
    have h_pair_W : (a', b') ∈ W := by
      have : (a', b') ∈ Set.prod U' V' := by
        exact ⟨hU₀_sub ha'U₀, hV₀_sub hb'V₀⟩
      exact hUV'_sub this
    -- the pair `(a', b')` lies in `interior (A ×ˢ B)`
    have h_pair_int : (a', b') ∈ interior (Set.prod A B) := by
      -- open set `S = interior A ×ˢ interior B`
      let S : Set (X × Y) := Set.prod (interior A) (interior B)
      have hS_open : IsOpen S := (isOpen_interior).prod isOpen_interior
      have hS_sub  : (S : Set (X × Y)) ⊆ Set.prod A B := by
        intro q hq
        rcases hq with ⟨hqA, hqB⟩
        exact ⟨interior_subset hqA, interior_subset hqB⟩
      have hInS : (a', b') ∈ S := by
        dsimp [S]; exact ⟨ha'intA, hb'intB⟩
      have hIn_intS : (a', b') ∈ interior S := by
        simpa [hS_open.interior_eq] using hInS
      exact (interior_mono hS_sub) hIn_intS
    exact ⟨(a', b'), h_pair_W, h_pair_int⟩
  -- `U` is an open set containing `(x, y)` and contained in the closure,
  -- hence `(x, y)` belongs to the interior of that closure
  have hxy :
      (x, y) ∈ interior (closure (interior (Set.prod A B))) :=
    (interior_maximal hU_sub hU_open) hpU
  exact hxy

theorem P1_sUnion_of_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsClosed A ∧ P1 A) → P1 (⋃₀ 𝒜) := by
  intro h
  apply P1_sUnion
  intro A hA
  exact (h A hA).2

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (Set.prod A B) := by
  intro hA hB
  -- Unfold the definitions of `P3`
  unfold P3 at hA hB ⊢
  intro p hp
  -- Split the components of the point `p`
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Use the hypotheses `P3 A` and `P3 B`
  have hx : x ∈ interior (closure A) := hA hxA
  have hy : y ∈ interior (closure B) := hB hyB
  -- Consider the product of the two open sets
  let S : Set (X × Y) := Set.prod (interior (closure A)) (interior (closure B))
  have hS_open : IsOpen (S : Set (X × Y)) :=
    (isOpen_interior).prod isOpen_interior
  have hpS : (x, y) ∈ S := by
    dsimp [S] at *
    exact ⟨hx, hy⟩
  -- Show that `S ⊆ closure (A ×ˢ B)`
  have hS_subset : (S : Set (X × Y)) ⊆ closure (Set.prod A B) := by
    intro z hz
    -- Split `z`
    rcases z with ⟨u, v⟩
    dsimp [S] at hz
    rcases hz with ⟨hu_int, hv_int⟩
    have hu_cl : u ∈ closure A := interior_subset hu_int
    have hv_cl : v ∈ closure B := interior_subset hv_int
    -- Show `(u, v)` lies in the closure of `A × B`
    have : (u, v) ∈ closure (Set.prod A B) := by
      -- Use the neighbourhood characterization of the closure
      apply (mem_closure_iff).2
      intro W hW hWuv
      -- Obtain a rectangular neighbourhood contained in `W`
      have hW_nhds : (W : Set (X × Y)) ∈ nhds (u, v) := IsOpen.mem_nhds hW hWuv
      rcases (mem_nhds_prod_iff).1 hW_nhds with
        ⟨U, hU_nhds, V, hV_nhds, hUV_sub⟩
      -- Refine the neighbourhoods around `u` and `v`
      rcases (mem_nhds_iff).1 hU_nhds with
        ⟨U₀, hU₀_sub, hU₀_open, huU₀⟩
      rcases (mem_nhds_iff).1 hV_nhds with
        ⟨V₀, hV₀_sub, hV₀_open, hvV₀⟩
      -- `U₀` meets `A`
      have hA_nonempty : (U₀ ∩ A).Nonempty := by
        have := (mem_closure_iff).1 hu_cl U₀ hU₀_open huU₀
        simpa using this
      rcases hA_nonempty with ⟨a, haU₀, haA⟩
      -- `V₀` meets `B`
      have hB_nonempty : (V₀ ∩ B).Nonempty := by
        have := (mem_closure_iff).1 hv_cl V₀ hV₀_open hvV₀
        simpa using this
      rcases hB_nonempty with ⟨b, hbV₀, hbB⟩
      -- The pair `(a, b)` is in `W`
      have habW : (a, b) ∈ W := by
        have : (a, b) ∈ Set.prod U V := by
          exact ⟨hU₀_sub haU₀, hV₀_sub hbV₀⟩
        exact hUV_sub this
      -- And `(a, b)` is in `A × B`
      have hab_prod : (a, b) ∈ Set.prod A B := by
        exact ⟨haA, hbB⟩
      exact ⟨(a, b), ⟨habW, hab_prod⟩⟩
    simpa using this
  -- Apply `interior_maximal`
  have hxy : (x, y) ∈ interior (closure (Set.prod A B)) :=
    (interior_maximal hS_subset hS_open) hpS
  exact hxy

theorem P3_of_dense_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → P3 A := by
  intro hDense
  -- First show that `closure A = univ`
  have hClosureA : (closure (A : Set X) : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    ·
      have hsubset : (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hDense] using hsubset
  -- Conclude `P3 A`
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hClosureA, interior_univ] using this

theorem P1_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) → P1 (Set.prod B A) := by
  intro hP1
  -- Unfold the definition of `P1`
  unfold P1 at hP1 ⊢
  intro p hpBA
  -- `q` is the point obtained by swapping the coordinates of `p`
  have hq_closure : ((p.2, p.1) : X × Y) ∈ closure (interior (Set.prod A B)) := by
    have hq_mem : ((p.2, p.1) : X × Y) ∈ Set.prod A B := by
      exact ⟨hpBA.2, hpBA.1⟩
    exact hP1 hq_mem
  -- We prove that `p` belongs to the required closure using the
  -- neighbourhood characterization.
  apply (mem_closure_iff).2
  intro U hU hpU
  -- `V` is the preimage of `U` by the swap map, it is an open set
  -- containing `q`.
  let V : Set (X × Y) := {q | Prod.swap q ∈ U}
  have hV_open : IsOpen V := by
    have h_cont : Continuous fun q : X × Y => Prod.swap q := continuous_swap
    have : IsOpen ((fun q : X × Y => Prod.swap q) ⁻¹' U) := hU.preimage h_cont
    simpa [V] using this
  have hqV : ((p.2, p.1) : X × Y) ∈ V := by
    dsimp [V]
    have h_eq : Prod.swap (p.2, p.1) = p := by
      cases p
      simp [Prod.swap]
    simpa [h_eq] using hpU
  -- Since `q` is in the closure, `V` meets `interior (A ×ˢ B)`.
  have h_nonempty : (V ∩ interior (Set.prod A B)).Nonempty := by
    have := (mem_closure_iff).1 hq_closure V hV_open hqV
    simpa [Set.inter_comm] using this
  rcases h_nonempty with ⟨w, hwV, hwIntAB⟩
  -- `w' = swap w` will lie in `U ∩ interior (B ×ˢ A)`.
  have hwU : Prod.swap w ∈ U := by
    dsimp [V] at hwV
    exact hwV
  -- Show that `Prod.swap w` is in the interior of `B ×ˢ A`.
  have hwIntBA : Prod.swap w ∈ interior (Set.prod B A) := by
    -- Auxiliary open set whose image is contained in `B ×ˢ A`.
    let U₂ : Set (Y × X) := {x | Prod.swap x ∈ interior (Set.prod A B)}
    have hU₂_open : IsOpen U₂ := by
      have h_cont : Continuous fun x : Y × X => Prod.swap x := continuous_swap
      have : IsOpen ((fun x : Y × X => Prod.swap x) ⁻¹' interior (Set.prod A B)) :=
        isOpen_interior.preimage h_cont
      simpa [U₂] using this
    have hU₂_sub : (U₂ : Set (Y × X)) ⊆ Set.prod B A := by
      intro x hx
      dsimp [U₂] at hx
      have h_swap_mem : Prod.swap x ∈ Set.prod A B := interior_subset hx
      rcases x with ⟨y, x'⟩
      dsimp [Prod.swap] at h_swap_mem
      rcases h_swap_mem with ⟨hx'A, hyB⟩
      exact ⟨hyB, hx'A⟩
    have h_mem_U₂ : Prod.swap w ∈ U₂ := by
      dsimp [U₂]
      have h_eq : Prod.swap (Prod.swap w) = w := by
        cases w
        simp [Prod.swap]
      simpa [h_eq] using hwIntAB
    have h_subset := interior_maximal hU₂_sub hU₂_open
    exact h_subset h_mem_U₂
  -- `Prod.swap w` witnesses the required non-emptiness.
  exact ⟨Prod.swap w, hwU, hwIntBA⟩

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) → P2 (Set.prod B A) := by
  intro hP2
  -- Unfold the definition of `P2`
  unfold P2 at hP2 ⊢
  intro p hpBA
  -- `p` lives in `B ×ˢ A`, hence its swap lives in `A ×ˢ B`
  have h_swap_mem : Prod.swap p ∈ Set.prod A B := by
    rcases hpBA with ⟨hpB, hpA⟩
    exact ⟨hpA, hpB⟩
  -- Use the hypothesis on the swapped point
  have h_swap_int :
      Prod.swap p ∈ interior (closure (interior (Set.prod A B))) :=
    hP2 h_swap_mem
  -- Define an auxiliary open set `S`
  let S : Set (Y × X) :=
      {q | Prod.swap q ∈ interior (closure (interior (Set.prod A B)))}
  have hS_open : IsOpen (S : Set (Y × X)) := by
    have : IsOpen
        ((fun q : Y × X => Prod.swap q) ⁻¹'
          interior (closure (interior (Set.prod A B)))) :=
      (isOpen_interior).preimage continuous_swap
    simpa [S] using this
  have hpS : p ∈ S := by
    dsimp [S]
    simpa using h_swap_int
  -- Show that `S ⊆ closure (interior (B ×ˢ A))`
  have hS_subset :
      (S : Set (Y × X)) ⊆ closure (interior (Set.prod B A)) := by
    intro z hz
    -- Information carried by `hz`
    have hz_swap :
        Prod.swap z ∈ interior (closure (interior (Set.prod A B))) := by
      dsimp [S] at hz
      exact hz
    have hz_clos :
        Prod.swap z ∈ closure (interior (Set.prod A B)) :=
      (interior_subset) hz_swap
    -- Prove that `z` belongs to the required closure
    apply (mem_closure_iff).2
    intro U hU hzU
    -- Preimage of `U` under `Prod.swap`
    let V : Set (X × Y) := {q | Prod.swap q ∈ U}
    have hV_open : IsOpen (V : Set (X × Y)) := by
      have : IsOpen ((fun q : X × Y => Prod.swap q) ⁻¹' U) :=
        hU.preimage continuous_swap
      simpa [V] using this
    have hzV : Prod.swap z ∈ V := by
      dsimp [V] ; simpa using hzU
    -- Since `Prod.swap z` is in the closure, `V` meets `interior (A ×ˢ B)`
    have h_nonempty :
        (V ∩ interior (Set.prod A B)).Nonempty := by
      have := (mem_closure_iff).1 hz_clos V hV_open hzV
      simpa [Set.inter_comm] using this
    rcases h_nonempty with ⟨w, hwV, hwIntAB⟩
    -- `Prod.swap w` lies in `U`
    have hwU : Prod.swap w ∈ U := by
      dsimp [V] at hwV ; exact hwV
    -- Show that `Prod.swap w` is in `interior (B ×ˢ A)`
    have hwIntBA : Prod.swap w ∈ interior (Set.prod B A) := by
      -- Auxiliary set to transport interior through the swap
      let U₂ : Set (Y × X) := {x | Prod.swap x ∈ interior (Set.prod A B)}
      have hU₂_open : IsOpen (U₂ : Set (Y × X)) := by
        have : IsOpen ((fun x : Y × X => Prod.swap x) ⁻¹'
            interior (Set.prod A B)) :=
          (isOpen_interior).preimage continuous_swap
        simpa [U₂] using this
      have hU₂_sub : (U₂ : Set (Y × X)) ⊆ Set.prod B A := by
        intro x hx
        dsimp [U₂] at hx
        have h_swap_mem : Prod.swap x ∈ Set.prod A B := interior_subset hx
        rcases x with ⟨y, x'⟩
        dsimp [Prod.swap] at h_swap_mem
        rcases h_swap_mem with ⟨hx'A, hyB⟩
        exact ⟨hyB, hx'A⟩
      have h_mem_U₂ : Prod.swap w ∈ U₂ := by
        dsimp [U₂]
        have : Prod.swap (Prod.swap w) = w := by
          cases w ; simp [Prod.swap]
        simpa [this] using hwIntAB
      exact (interior_maximal hU₂_sub hU₂_open) h_mem_U₂
    -- Provide the witness in `U ∩ interior (B ×ˢ A)`
    exact ⟨Prod.swap w, hwU, hwIntBA⟩
  -- Conclude using `interior_maximal`
  have hp_int :
      p ∈ interior (closure (interior (Set.prod B A))) :=
    (interior_maximal hS_subset hS_open) hpS
  exact hp_int

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) → P3 (Set.prod B A) := by
  intro hP3
  -- unfold the definition of `P3`
  unfold P3 at hP3 ⊢
  intro p hpBA
  -- the swapped point lives in `A ×ˢ B`
  have h_swap_mem : Prod.swap p ∈ Set.prod A B := by
    rcases hpBA with ⟨hpB, hpA⟩
    exact ⟨hpA, hpB⟩
  -- apply the hypothesis to the swapped point
  have h_swap_int : Prod.swap p ∈ interior (closure (Set.prod A B)) :=
    hP3 h_swap_mem
  -- define an auxiliary open set
  let S : Set (Y × X) := {q | Prod.swap q ∈ interior (closure (Set.prod A B))}
  have hS_open : IsOpen (S : Set (Y × X)) := by
    have :
        IsOpen
          ((fun q : Y × X => Prod.swap q) ⁻¹'
            interior (closure (Set.prod A B))) :=
      (isOpen_interior).preimage continuous_swap
    simpa [S] using this
  have hpS : p ∈ S := by
    dsimp [S]
    simpa using h_swap_int
  -- show that `S ⊆ closure (B ×ˢ A)`
  have hS_subset : (S : Set (Y × X)) ⊆ closure (Set.prod B A) := by
    intro z hz
    -- information on `Prod.swap z`
    have hz_swap :
        Prod.swap z ∈ interior (closure (Set.prod A B)) := by
      dsimp [S] at hz
      exact hz
    have hz_clos :
        Prod.swap z ∈ closure (Set.prod A B) :=
      interior_subset hz_swap
    -- neighbourhood characterization of the closure
    apply (mem_closure_iff).2
    intro U hU hzU
    -- preimage of `U` under the swap map
    let V : Set (X × Y) := {q | Prod.swap q ∈ U}
    have hV_open : IsOpen (V : Set (X × Y)) := by
      have : IsOpen ((fun q : X × Y => Prod.swap q) ⁻¹' U) :=
        hU.preimage continuous_swap
      simpa [V] using this
    have hzV : Prod.swap z ∈ V := by
      dsimp [V] ; simpa using hzU
    -- `V` meets `A ×ˢ B`
    have h_nonempty : (V ∩ Set.prod A B).Nonempty := by
      have := (mem_closure_iff).1 hz_clos V hV_open hzV
      simpa [Set.inter_comm] using this
    rcases h_nonempty with ⟨w, hwV, hwAB⟩
    -- the swapped point belongs to `U ∩ (B ×ˢ A)`
    have hwU : Prod.swap w ∈ U := by
      dsimp [V] at hwV
      exact hwV
    have hwBA : Prod.swap w ∈ Set.prod B A := by
      rcases w with ⟨a, b⟩
      dsimp [Prod.swap] at *
      rcases hwAB with ⟨haA, hbB⟩
      exact ⟨hbB, haA⟩
    exact ⟨Prod.swap w, hwU, hwBA⟩
  -- conclude using `interior_maximal`
  exact (interior_maximal hS_subset hS_open) hpS

theorem P1_sUnion_of_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsOpen A ∧ P1 A) → P1 (⋃₀ 𝒜) := by
  intro h
  apply P1_sUnion
  intro A hA
  exact (h A hA).2

theorem P2_sUnion_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsClosed A ∧ P2 A) → P2 (⋃₀ 𝒜) := by
  intro h
  apply P2_sUnion
  intro A hA
  exact (h A hA).2

theorem P2_prod_same {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (Set.prod A A) ↔ P2 A := by
  constructor
  · intro hProd
    -- We turn `hProd` into a pointwise statement.
    -- Unfold the definition of `P2`.
    unfold P2 at hProd ⊢
    intro x hxA
    -- Apply the hypothesis to the diagonal point `(x, x)`.
    have hxx :
        (x, x) ∈ interior (closure (interior (Set.prod A A))) :=
      hProd ⟨hxA, hxA⟩
    -- The set that appears on the right-hand side is open.
    have hO_open :
        IsOpen (interior (closure (interior (Set.prod A A))) :
          Set (X × X)) :=
      isOpen_interior
    -- Hence it is a neighbourhood of `(x, x)`.
    have hO_nhds :
        (interior (closure (interior (Set.prod A A))) :
          Set (X × X)) ∈ nhds (x, x) :=
      hO_open.mem_nhds hxx
    -- Using the product neighbourhood basis, pick rectangular neighbourhoods.
    rcases (mem_nhds_prod_iff).1 hO_nhds with
      ⟨U, hU_nhds, V, hV_nhds, hUV_sub⟩
    -- Further shrink these neighbourhoods.
    rcases (mem_nhds_iff).1 hU_nhds with
      ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
    rcases (mem_nhds_iff).1 hV_nhds with
      ⟨V₀, hV₀_sub, hV₀_open, hxV₀⟩
    -- Define the open neighbourhood `W := U₀ ∩ V₀` of `x`.
    let W : Set X := U₀ ∩ V₀
    have hW_open : IsOpen (W : Set X) := hU₀_open.inter hV₀_open
    have hxW : x ∈ W := by
      dsimp [W]; exact ⟨hxU₀, hxV₀⟩
    -- First, observe that `U₀ × V₀` is contained in the big open set.
    have hProdSub :
        (Set.prod U₀ V₀ : Set (X × X)) ⊆
          interior (closure (interior (Set.prod A A))) :=
      (Set.prod_mono hU₀_sub hV₀_sub).trans hUV_sub
    -- We show that every point of `W` lies in `closure (interior A)`.
    have hW_subset : (W : Set X) ⊆ closure (interior A) := by
      intro y hyW
      -- The pair `(y, y)` is in the big open set.
      have hyPair :
          (y, y) ∈ interior (closure (interior (Set.prod A A))) := by
        have : (y, y) ∈ (Set.prod U₀ V₀) := by
          exact ⟨hyW.1, hyW.2⟩
        exact hProdSub this
      -- Therefore `(y, y)` is in the closure of `interior (A × A)`.
      have hyPairClos :
          (y, y) ∈ closure (interior (Set.prod A A)) :=
        interior_subset hyPair
      -- Use the characterization of the closure.
      apply (mem_closure_iff).2
      intro S hS hyS
      -- Consider the open set `S × S`.
      have hSS_open : IsOpen (Set.prod S S : Set (X × X)) := hS.prod hS
      have hyPairInSS : (y, y) ∈ Set.prod S S := by
        exact ⟨hyS, hyS⟩
      -- Since `(y, y)` is in the closure, the intersection is non-empty.
      have hNonempty :
          ((Set.prod S S) ∩ interior (Set.prod A A)).Nonempty :=
        (mem_closure_iff).1 hyPairClos _ hSS_open hyPairInSS
      -- Extract a witness `(a, b)`.
      rcases hNonempty with ⟨w, hwSS, hwInt⟩
      rcases w with ⟨a, b⟩
      -- The first coordinate `a` belongs to `S`.
      have haS : a ∈ S := hwSS.1
      -- From `hwInt` we deduce `a ∈ interior A`.
      have haIntA : a ∈ interior A := by
        -- `hwInt` says `(a, b)` is in `interior (A × A)`.
        -- Use neighbourhoods to produce an open set contained in `A`.
        have hInt := hwInt
        have hInt_nhds :
            (interior (Set.prod A A) : Set (X × X)) ∈ nhds (a, b) :=
          isOpen_interior.mem_nhds hInt
        rcases (mem_nhds_prod_iff).1 hInt_nhds with
          ⟨O₁, hO₁_nhds, O₂, hO₂_nhds, hProdSub₂⟩
        rcases (mem_nhds_iff).1 hO₁_nhds with
          ⟨O₁', hO₁'_sub, hO₁'_open, haO₁'⟩
        -- `O₁'` is an open neighbourhood of `a` contained in `A`.
        have hO₁'_subA : (O₁' : Set X) ⊆ A := by
          intro z hz
          have hzO₁ : z ∈ O₁ := hO₁'_sub hz
          have hbO₂ : b ∈ O₂ := mem_of_mem_nhds hO₂_nhds
          have hzPair : (z, b) ∈ Set.prod O₁ O₂ := ⟨hzO₁, hbO₂⟩
          have hzInt : (z, b) ∈ interior (Set.prod A A) := hProdSub₂ hzPair
          have hzProd : (z, b) ∈ Set.prod A A := interior_subset hzInt
          exact hzProd.1
        -- Hence `a` is in `interior A`.
        exact (interior_maximal hO₁'_subA hO₁'_open) haO₁'
      -- `S` meets `interior A`, so `y` is in the closure.
      exact ⟨a, haS, haIntA⟩
    -- `W` is an open neighbourhood of `x` contained in the desired set,
    -- so `x` belongs to the interior.
    have hxInt :
        x ∈ interior (closure (interior A)) :=
      (interior_maximal hW_subset hW_open) hxW
    exact hxInt
  · intro hA
    -- The reverse implication follows from `P2_prod`.
    exact (P2_prod (A := A) (B := A)) hA hA

theorem exists_P1_proper_subset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : A.Nonempty) : ∃ B, B ⊂ A ∧ P1 B := by
  refine ⟨(∅ : Set X), ?_, P1_empty⟩
  have hsub : (∅ : Set X) ⊆ A := Set.empty_subset _
  have hnot : ¬ A ⊆ (∅ : Set X) := by
    intro h
    rcases hA with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := h hx
    exact this
  exact ⟨hsub, hnot⟩

theorem P1_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  unfold P1
  intro x hx
  have hsubset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A))) := by
    have hInner :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    exact closure_mono hInner
  exact hsubset hx

theorem P1_union_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (A ∪ A) ↔ P1 A := by
  simpa [Set.union_self]

theorem P2_union_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (A ∪ A) ↔ P2 A := by
  simpa [Set.union_self]

theorem P3_union_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (A ∪ A) ↔ P3 A := by
  simpa [Set.union_self]

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {A : Set X} : P1 A → P1 (h '' A) := by
  intro hP1
  -- unpack the definition of `P1`
  unfold P1 at hP1 ⊢
  intro y hy
  -- pick a preimage point
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the closure of `interior A`
  have hx_cl : (x : X) ∈ closure (interior A) := hP1 hxA
  -- first, put `h x` in `closure (h '' interior A)`
  have h_mem_small : (h x : Y) ∈ closure (h '' interior A) := by
    -- image of the closure under a homeomorphism
    have h_image_eq :
        (h '' closure (interior A) : Set Y) =
          closure (h '' interior A) := by
      simpa using h.image_closure (interior A)
    have : (h x : Y) ∈ h '' closure (interior A) := ⟨x, hx_cl, rfl⟩
    simpa [h_image_eq] using this
  -- show that `h '' interior A ⊆ interior (h '' A)`
  have h_subset : (h '' interior A : Set Y) ⊆ interior (h '' A) := by
    -- the image of an open set by a homeomorphism is open
    have h_open_image_int : IsOpen (h '' interior A : Set Y) := by
      -- express it as the preimage of an open set by the continuous inverse
      have h_eq :
          (h '' interior A : Set Y) =
            {y : Y | h.symm y ∈ interior A} := by
        ext y
        constructor
        · rintro ⟨x, hxIntA, rfl⟩
          simpa using hxIntA
        · intro hy
          have hxIntA : h.symm y ∈ interior A := hy
          refine ⟨h.symm y, hxIntA, ?_⟩
          have : h (h.symm y) = y := h.apply_symm_apply y
          simpa [this]
      have h_preopen :
          IsOpen ((fun y : Y => h.symm y) ⁻¹' interior A) :=
        isOpen_interior.preimage h.symm.continuous
      simpa [Set.preimage, h_eq] using h_preopen
    -- and it is clearly contained in `h '' A`
    have h_sub : (h '' interior A : Set Y) ⊆ h '' A := by
      intro y hy
      rcases hy with ⟨x, hxIntA, rfl⟩
      exact ⟨x, interior_subset hxIntA, rfl⟩
    exact interior_maximal h_sub h_open_image_int
  -- use monotonicity of the closure
  have h_closure_mono :
      closure (h '' interior A : Set Y) ⊆ closure (interior (h '' A)) :=
    closure_mono h_subset
  exact h_closure_mono h_mem_small

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {A : Set X} : P2 A → P2 (h '' A) := by
  intro hP2
  -- Unfold the definition of `P2`
  unfold P2 at hP2 ⊢
  intro y hy
  -- Pick a preimage point `x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies the property coming from `P2 A`
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hP2 hxA
  -- Define the auxiliary open set `O`
  let O : Set Y := h '' interior (closure (interior A))
  -- `O` is open since `h` is a homeomorphism (hence an open map)
  have hO_open : IsOpen (O : Set Y) := by
    have h_open : IsOpen (interior (closure (interior A)) : Set X) :=
      isOpen_interior
    simpa [O] using h.isOpenMap.image h_open
  -- We show that `O ⊆ closure (interior (h '' A))`
  have hO_sub : (O : Set Y) ⊆ closure (interior (h '' A)) := by
    -- First, show that `h '' interior A ⊆ interior (h '' A)`
    have h_img_int_subset :
        (h '' interior A : Set Y) ⊆ interior (h '' A) := by
      -- The image of an open set by a homeomorphism is open
      have h_open_img : IsOpen (h '' interior A : Set Y) := by
        have h_open_int : IsOpen (interior A : Set X) := isOpen_interior
        simpa using h.isOpenMap.image h_open_int
      -- And it is obviously contained in `h '' A`
      have h_sub : (h '' interior A : Set Y) ⊆ h '' A := by
        intro z hz
        rcases hz with ⟨x', hx'int, rfl⟩
        exact ⟨x', interior_subset hx'int, rfl⟩
      exact interior_maximal h_sub h_open_img
    -- Hence, by `closure_mono`,
    have h_closure_sub :
        closure (h '' interior A : Set Y) ⊆ closure (interior (h '' A)) :=
      closure_mono h_img_int_subset
    -- Finally, relate `O` to `closure (h '' interior A)`
    intro z hz
    dsimp [O] at hz
    rcases hz with ⟨x', hx'Int, rfl⟩
    -- `h x'` is in `h '' closure (interior A)`
    have hz_in_closure :
        (h x' : Y) ∈ closure (h '' interior A) := by
      have : (h x' : Y) ∈ h '' closure (interior A) :=
        ⟨x', interior_subset hx'Int, rfl⟩
      simpa [h.image_closure (interior A)] using this
    exact h_closure_sub hz_in_closure
  -- Our point belongs to `O`
  have hxO : (h x : Y) ∈ O := by
    dsimp [O]
    exact ⟨x, hx_int, rfl⟩
  -- Since `O` is open and contained in the target set, we conclude
  have hIncl :
      (h x : Y) ∈ interior (closure (interior (h '' A))) :=
    (interior_maximal hO_sub hO_open) hxO
  exact hIncl

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {A : Set X} : P3 A → P3 (h '' A) := by
  intro hP3
  -- Unfold the definition of `P3`
  unfold P3 at hP3 ⊢
  intro y hyImage
  -- Choose a preimage point `x` such that `h x = y`
  rcases hyImage with ⟨x, hxA, rfl⟩
  -- From `P3 A` we know that `x ∈ interior (closure A)`
  have hxInt : (x : X) ∈ interior (closure A) := hP3 hxA
  -- Show that `h '' interior (closure A)` is contained in
  -- `interior (closure (h '' A))`
  have h_subset :
      (h '' interior (closure A) : Set Y) ⊆ interior (closure (h '' A)) := by
    -- The image of an open set by a homeomorphism is open
    have h_open :
        IsOpen (h '' interior (closure A) : Set Y) := by
      have h_open_src : IsOpen (interior (closure A) : Set X) :=
        isOpen_interior
      simpa using h.isOpenMap.image h_open_src
    -- And it is contained in the closure of `h '' A`
    have h_sub :
        (h '' interior (closure A) : Set Y) ⊆ closure (h '' A) := by
      intro z hz
      rcases hz with ⟨x', hx'int, rfl⟩
      -- `x'` lies in `interior (closure A)` so it lies in `closure A`
      have : (h x' : Y) ∈ h '' closure A := ⟨x', interior_subset hx'int, rfl⟩
      -- Use the lemma `image_closure` for a homeomorphism
      have h_eq : (h '' closure A : Set Y) = closure (h '' A) := by
        simpa using h.image_closure A
      simpa [h_eq] using this
    -- Conclude using `interior_maximal`
    exact interior_maximal h_sub h_open
  -- Our point `h x` belongs to `h '' interior (closure A)`
  have hxImage : (h x : Y) ∈ h '' interior (closure A) := ⟨x, hxInt, rfl⟩
  -- Therefore it belongs to the required interior
  exact h_subset hxImage

theorem open_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 A → IsOpen A := by
  intro hClosed hP2
  -- `P2` gives the inclusion `A ⊆ interior (closure (interior A))`.
  have h₁ : (A : Set X) ⊆ interior (closure (interior A)) := hP2
  -- Since `A` is closed and `interior A ⊆ A`, we get
  -- `closure (interior A) ⊆ A`.
  have h_closure_subset : closure (interior A) ⊆ A := by
    have h : (interior A : Set X) ⊆ A := interior_subset
    -- `closure_minimal` upgrades this to an inclusion on closures.
    exact closure_minimal h hClosed
  -- By monotonicity of `interior`,
  have h₂ : interior (closure (interior A)) ⊆ interior A :=
    interior_mono h_closure_subset
  -- Combining the two inclusions yields `A ⊆ interior A`.
  have hA_int : (A : Set X) ⊆ interior A := fun x hx => h₂ (h₁ hx)
  -- Together with the obvious `interior A ⊆ A`, we get equality.
  have h_eq : interior A = A :=
    Set.Subset.antisymm (interior_subset : interior A ⊆ A) hA_int
  -- Therefore `A` is open.
  simpa [h_eq] using (isOpen_interior : IsOpen (interior A))

theorem P1_iff_P2_iff_P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A ↔ P2 A ∧ P3 A := by
  constructor
  · intro _hP1
    exact ⟨P2_subsingleton (A := A), P3_subsingleton (A := A)⟩
  · intro _h
    exact P1_subsingleton (A := A)

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) ↔ P2 (Set.prod B A) := by
  constructor
  · intro h
    exact (P2_prod_swap (A := A) (B := B)) h
  · intro h
    exact (P2_prod_swap (X := Y) (Y := X) (A := B) (B := A)) h

theorem P3_prod_self {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (Set.prod A A) ↔ P3 A := by
  constructor
  · intro hProd
    -- we prove `P3 A`
    unfold P3 at hProd ⊢
    intro x hxA
    -- the point `(x, x)` lies in `A ×ˢ A`
    have hx_pair : (x, x) ∈ Set.prod A A := by
      exact ⟨hxA, hxA⟩
    -- hence it belongs to the open set appearing in `P3`
    have hxx :
        (x, x) ∈ interior (closure (Set.prod A A)) := hProd hx_pair
    -- the open neighbourhood provided by `P3`
    have hO_open :
        IsOpen (interior (closure (Set.prod A A)) : Set (X × X)) :=
      isOpen_interior
    have hO_nhds :
        (interior (closure (Set.prod A A)) : Set (X × X)) ∈ nhds (x, x) :=
      hO_open.mem_nhds hxx
    -- obtain rectangular neighbourhoods
    rcases (mem_nhds_prod_iff).1 hO_nhds with
      ⟨U, hU_nhds, V, hV_nhds, hUV_sub⟩
    rcases (mem_nhds_iff).1 hU_nhds with
      ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
    rcases (mem_nhds_iff).1 hV_nhds with
      ⟨V₀, hV₀_sub, hV₀_open, hxV₀⟩
    -- define the open neighbourhood `W` of `x`
    let W : Set X := U₀ ∩ V₀
    have hW_open : IsOpen (W : Set X) := hU₀_open.inter hV₀_open
    have hxW : x ∈ W := by
      dsimp [W]; exact ⟨hxU₀, hxV₀⟩
    -- `U₀ ×ˢ V₀` is contained in the big open set
    have hProdSub :
        (Set.prod U₀ V₀ : Set (X × X)) ⊆
          interior (closure (Set.prod A A)) :=
      (Set.prod_mono hU₀_sub hV₀_sub).trans hUV_sub
    -- every point of `W` is in the closure of `A`
    have hW_subset : (W : Set X) ⊆ closure A := by
      intro y hyW
      -- `(y, y)` belongs to `U₀ ×ˢ V₀ ⊆ interior (closure (A × A))`
      have hy_pair :
          (y, y) ∈ interior (closure (Set.prod A A)) := by
        have : (y, y) ∈ Set.prod U₀ V₀ := by
          exact ⟨hyW.1, hyW.2⟩
        exact hProdSub this
      -- hence `(y, y)` is in the closure of `A × A`
      have hy_pair_cl :
          (y, y) ∈ closure (Set.prod A A) := interior_subset hy_pair
      -- use the neighbourhood characterization of the closure
      apply (mem_closure_iff).2
      intro S hS hyS
      -- consider `S ×ˢ S`
      let SS : Set (X × X) := Set.prod S S
      have hSS_open : IsOpen (SS : Set (X × X)) := hS.prod hS
      have h_pair_SS : (y, y) ∈ SS := by
        exact ⟨hyS, hyS⟩
      -- intersect with `A × A`
      have hNonempty :
          (SS ∩ Set.prod A A).Nonempty :=
        (mem_closure_iff).1 hy_pair_cl SS hSS_open h_pair_SS
      rcases hNonempty with ⟨⟨a, b⟩, hmem⟩
      have hSSmem : (a, b) ∈ SS := hmem.1
      have hABmem : (a, b) ∈ Set.prod A A := hmem.2
      -- `a` lies in `S ∩ A`
      exact
        ⟨a, hSSmem.1, hABmem.1⟩
    -- `W` is an open nbhd of `x` contained in `closure A`
    have hInt := interior_maximal hW_subset hW_open
    exact hInt hxW
  · intro hA
    -- the reverse implication follows from `P3_prod`
    simpa using (P3_prod (A := A) (B := A) hA hA)

theorem P1_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = closure A → P1 A := by
  intro hEq
  exact (P1_iff_closure_eq (A := A)).2 hEq

theorem P3_of_open_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (hopen : IsOpenMap f) {A : Set X} : P3 A → P3 (f '' A) := by
  intro hP3
  -- expand the definition of `P3`
  dsimp [P3] at hP3 ⊢
  -- we have to prove:  f '' A ⊆ interior (closure (f '' A))
  intro y hyImage
  -- choose a preimage point
  rcases hyImage with ⟨x, hxA, rfl⟩
  -- use the hypothesis `P3 A`
  have hxInt : (x : X) ∈ interior (closure A) := hP3 hxA
  ------------------------------------------------------------------
  -- 1.  the auxiliary open set  O := f '' interior (closure A)
  ------------------------------------------------------------------
  have hO_open : IsOpen (f '' interior (closure A) : Set Y) := by
    have h_src_open : IsOpen (interior (closure A) : Set X) := isOpen_interior
    exact hopen _ h_src_open
  ------------------------------------------------------------------
  -- 2.  show   O ⊆ closure (f '' A)
  ------------------------------------------------------------------
  have hO_subset : (f '' interior (closure A) : Set Y) ⊆ closure (f '' A) := by
    intro z hz
    rcases hz with ⟨x', hx'Int, rfl⟩
    -- `x'` lies in `closure A`
    have hx'Cl : (x' : X) ∈ closure A := interior_subset hx'Int
    -- we prove that `f x'` is in the closure of `f '' A`
    have : (f x' : Y) ∈ closure (f '' A) := by
      -- neighbourhood criterion for the closure
      apply (mem_closure_iff).2
      intro V hV hVfx
      -- the preimage of `V` is open
      have h_pre_open : IsOpen (f ⁻¹' V) := hV.preimage hf
      -- `x'` belongs to this preimage
      have hx'_pre : x' ∈ f ⁻¹' V := by
        simpa using hVfx
      -- since `x' ∈ closure A`, the intersection meets `A`
      have h_nonempty : ((f ⁻¹' V) ∩ A).Nonempty := by
        have h := (mem_closure_iff).1 hx'Cl (f ⁻¹' V) h_pre_open hx'_pre
        simpa [Set.inter_comm] using h
      rcases h_nonempty with ⟨x₁, hx₁_pre, hx₁A⟩
      -- provide the required witness in `V ∩ f '' A`
      exact
        ⟨f x₁, ⟨by
          simpa using hx₁_pre,
          ⟨x₁, hx₁A, rfl⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  -- 3.  `f x` lies in the interior of the target closure
  ------------------------------------------------------------------
  have hfx_mem_O : (f x : Y) ∈ f '' interior (closure A) := ⟨x, hxInt, rfl⟩
  have h_result : (f x : Y) ∈ interior (closure (f '' A)) :=
    (interior_maximal hO_subset hO_open) hfx_mem_O
  exact h_result

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → closure A = Set.univ → P2 A := by
  intro hClosed hDense
  have hA_univ : (A : Set X) = Set.univ := by
    have hCl : closure A = A := hClosed.closure_eq
    simpa [hCl] using hDense
  simpa [hA_univ] using (P2_univ : P2 (Set.univ : Set X))

theorem P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → closure A = Set.univ → P1 A := by
  intro hClosed hDense
  have hA_univ : (A : Set X) = Set.univ := by
    simpa [hClosed.closure_eq] using hDense
  simpa [hA_univ] using (P1_univ : P1 (Set.univ : Set X))

theorem P1_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) ↔ P1 (Set.prod B A) := by
  constructor
  · intro h
    exact (P1_prod_swap (A := A) (B := B)) h
  · intro h
    exact (P1_prod_swap (X := Y) (Y := X) (A := B) (B := A)) h

theorem P3_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) ↔ P3 (Set.prod B A) := by
  constructor
  · intro h
    exact (P3_prod_swap (A := A) (B := B)) h
  · intro h
    exact (P3_prod_swap (X := Y) (Y := X) (A := B) (B := A)) h

theorem P1_prod_self {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (Set.prod A A) ↔ P1 A := by
  constructor
  · intro hProd
    -- Unfold the definition of `P1`.
    unfold P1 at hProd ⊢
    intro x hxA
    -- From `hProd` we know that `(x,x)` is in the closure of the interior of
    -- `A ×ˢ A`.
    have hx_pair : (x, x) ∈ closure (interior (Set.prod A A)) :=
      hProd ⟨hxA, hxA⟩
    -- Use the neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro U hU hxU
    -- Consider the rectangular neighbourhood `U ×ˢ U` of `(x,x)`.
    have hW_open : IsOpen (Set.prod U U : Set (X × X)) := hU.prod hU
    have hxW : (x, x) ∈ Set.prod U U := by
      exact ⟨hxU, hxU⟩
    -- `U ×ˢ U` meets `interior (A ×ˢ A)`.
    have h_nonempty :
        ((Set.prod U U) ∩ interior (Set.prod A A)).Nonempty :=
      (mem_closure_iff).1 hx_pair _ hW_open hxW
    rcases h_nonempty with ⟨⟨a, b⟩, h_ab_W, h_ab_int⟩
    have haU : a ∈ U := h_ab_W.1
    -- Work in a product neighbourhood of `(a,b)` contained in `A ×ˢ A`.
    have h_int_nhds :
        (interior (Set.prod A A) : Set (X × X)) ∈ nhds (a, b) :=
      isOpen_interior.mem_nhds h_ab_int
    rcases (mem_nhds_prod_iff).1 h_int_nhds with
      ⟨U₁, hU₁_nhds, V₁, hV₁_nhds, h_sub⟩
    rcases (mem_nhds_iff).1 hU₁_nhds with
      ⟨U₂, hU₂_sub, hU₂_open, haU₂⟩
    -- Show that `U₂ ⊆ A`.
    have hU₂_A : (U₂ : Set X) ⊆ A := by
      intro z hz
      have hbV₁ : b ∈ V₁ := mem_of_mem_nhds hV₁_nhds
      have hz_prod : (z, b) ∈ Set.prod U₁ V₁ := ⟨hU₂_sub hz, hbV₁⟩
      have hz_int : (z, b) ∈ interior (Set.prod A A) := h_sub hz_prod
      have hz_prodAA : (z, b) ∈ Set.prod A A :=
        interior_subset hz_int
      exact hz_prodAA.1
    -- Therefore `a ∈ interior A`.
    have ha_intA : a ∈ interior A :=
      (interior_maximal hU₂_A hU₂_open) haU₂
    -- Provide the witness `(a)` for the closure condition.
    exact ⟨a, haU, ha_intA⟩
  · intro hA
    -- Use the already proven `P1_prod`.
    have : P1 (Set.prod A A) := P1_prod (A := A) (B := A) hA hA
    simpa using this

theorem exists_P3_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ U ⊆ A ∧ P3 U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  simpa using (P3_interior (A := A))

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  -- Since `A` is closed we have `closure A = A`.
  have hClosure : (closure (A : Set X)) = A := hA.closure_eq
  constructor
  · -- First direction:  `P2 A → P3 A`
    intro hP2
    -- Unfold `P3`
    intro x hxA
    -- Use `P2` to put `x` in the open set `interior (closure (interior A))`.
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
    -- Because `A` is closed, `closure (interior A) ⊆ A`.
    have hSub : (closure (interior A) : Set X) ⊆ A :=
      closure_minimal (interior_subset : (interior A : Set X) ⊆ A) hA
    -- Hence the interiors satisfy the same inclusion.
    have hIntSub :
        (interior (closure (interior A)) : Set X) ⊆ interior A :=
      interior_mono hSub
    -- Place `x` in `interior A`, then rewrite using `closure A = A`.
    have hxIntA : x ∈ interior A := hIntSub hx₁
    simpa [hClosure] using hxIntA
  · -- Second direction:  `P3 A → P2 A`
    intro hP3
    -- First prove that `A` is open.
    have hOpenA : IsOpen (A : Set X) := by
      -- Show `interior A = A`.
      have hEq : interior A = A := by
        apply Set.Subset.antisymm interior_subset
        intro x hxA
        have hxIntCl : x ∈ interior (closure A) := hP3 hxA
        simpa [hClosure] using hxIntCl
      simpa [hEq] using (isOpen_interior : IsOpen (interior A))
    -- On an open set, `P2` holds by `P2_of_open`.
    exact P2_of_open (A := A) hOpenA

theorem exists_P1_compact_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, K ⊆ A ∧ IsCompact K ∧ P1 K := by
  refine ⟨(∅ : Set X), Set.empty_subset _, isCompact_empty, P1_empty⟩

theorem P3_of_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 A → P3 A := by
  intro hClosed hP2
  exact ((P2_iff_P3_of_closed (A := A) hClosed).1 hP2)

theorem P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (closure A) → P3 A := by
  intro hP3
  intro x hxA
  have : (x : X) ∈ interior (closure (closure A)) :=
    hP3 (subset_closure hxA)
  simpa [closure_closure] using this

theorem P3_sUnion_of_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsOpen A ∧ P3 A) → P3 (⋃₀ 𝒜) := by
  intro h
  apply P3_sUnion
  intro A hA
  exact (h A hA).2

theorem P1_prod_of_P2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P1 (Set.prod A B) := by
  intro hA hB
  have hA' : P1 A := (P2_subset_P1 (A := A)) hA
  have hB' : P1 B := (P2_subset_P1 (A := B)) hB
  exact P1_prod hA' hB'

theorem P2_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior (closure A)) = closure A := by
  intro hP2
  -- From `P2 A` we get `P1 A`.
  have hP1 : P1 A := (P2_subset_P1 (A := A)) hP2
  -- Hence, `P1 (closure A)`.
  have hP1Cl : P1 (closure A) := P1_closure (A := A) hP1
  -- Use the characterization `P1 S ↔ closure (interior S) = closure S`
  have hEq : closure (interior (closure A)) = closure (closure A) :=
    (P1_iff_closure_eq (A := closure A)).1 hP1Cl
  simpa [closure_closure] using hEq

theorem P2_closed_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → IsClosed A → closure (interior A) = A := by
  intro hP2 hClosed
  have hP1 : P1 A := (P2_subset_P1 (A := A)) hP2
  exact (P1_eq_of_closed (A := A)) hClosed hP1

theorem P2_of_open_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (hopen : IsOpenMap f) {A : Set X} : P2 A → P2 (f '' A) := by
  intro hP2
  -- Unfold the definition of `P2`
  unfold P2 at hP2 ⊢
  intro y hyImage
  -- Choose a preimage point `x`
  rcases hyImage with ⟨x, hxA, rfl⟩
  -- From `P2 A` we have the required property for `x`
  have hxInt : (x : X) ∈ interior (closure (interior A)) := hP2 hxA
  -- Define the auxiliary open set `O`
  set O : Set Y := f '' interior (closure (interior A)) with hOdef
  have hO_open : IsOpen (O : Set Y) := by
    have hOpenSrc : IsOpen (interior (closure (interior A)) : Set X) :=
      isOpen_interior
    simpa [hOdef] using hopen _ hOpenSrc
  -- Show  `O ⊆ closure (interior (f '' A))`
  have hO_subset : (O : Set Y) ⊆ closure (interior (f '' A)) := by
    intro z hz
    rcases hz with ⟨x', hx'Int, rfl⟩
    -- First step:  `f x'` is in the closure of `f '' interior A`
    have h1 : (f x' : Y) ∈ closure (f '' interior A) := by
      -- Since `x' ∈ closure (interior A)`
      have hx'Cl : (x' : X) ∈ closure (interior A) :=
        interior_subset hx'Int
      -- Use the neighbourhood characterization of the closure
      apply (mem_closure_iff).2
      intro V hV hVfx
      -- The preimage of `V` is open
      have hPreOpen : IsOpen (f ⁻¹' V) := hV.preimage hf
      have hx'Pre : x' ∈ f ⁻¹' V := by
        simpa using hVfx
      -- Intersect with `interior A`
      have hNonempty :
          ((f ⁻¹' V) ∩ interior A).Nonempty := by
        have := (mem_closure_iff).1 hx'Cl (f ⁻¹' V) hPreOpen hx'Pre
        simpa [Set.inter_comm] using this
      rcases hNonempty with ⟨x₁, hx₁Pre, hx₁IntA⟩
      exact
        ⟨f x₁, ⟨by
          simpa using hx₁Pre,
          ⟨x₁, hx₁IntA, rfl⟩⟩⟩
    -- Second step:  `closure (f '' interior A) ⊆ closure (interior (f '' A))`
    have hIncl :
        closure (f '' interior A : Set Y) ⊆
          closure (interior (f '' A)) := by
      -- Prove the basic inclusion `f '' interior A ⊆ interior (f '' A)`
      have h_img_subset :
          (f '' interior A : Set Y) ⊆ interior (f '' A) := by
        -- The image of an open set is open
        have hOpenImg : IsOpen (f '' interior A : Set Y) := by
          have hOpenSrc : IsOpen (interior A : Set X) := isOpen_interior
          simpa using hopen _ hOpenSrc
        -- And it is contained in `f '' A`
        have hSub : (f '' interior A : Set Y) ⊆ f '' A := by
          intro w hw
          rcases hw with ⟨x₂, hx₂Int, rfl⟩
          exact ⟨x₂, interior_subset hx₂Int, rfl⟩
        -- Apply `interior_maximal`
        exact interior_maximal hSub hOpenImg
      exact closure_mono h_img_subset
    exact hIncl h1
  -- Our original point belongs to `O`
  have hyO : (f x : Y) ∈ O := by
    dsimp [O] at hOdef
    simpa [hOdef] using ⟨x, hxInt, rfl⟩
  -- Conclude using `interior_maximal`
  have : (f x : Y) ∈ interior (closure (interior (f '' A))) :=
    (interior_maximal hO_subset hO_open) hyO
  exact this

theorem open_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → IsOpen A := by
  intro hClosed hP3
  -- obtain `P2 A` from `P3 A` since `A` is closed
  have hP2 : P2 A := ((P2_iff_P3_of_closed (A := A) hClosed).2) hP3
  -- use the previous result for `P2` on closed sets
  exact open_of_P2_closed (A := A) hClosed hP2

theorem P3_of_dense_interior_closure' {X : Type*} [TopologicalSpace X] {A : Set X} : interior (closure A) = Set.univ → P3 A := by
  intro hInt
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hInt] using this

theorem P2_sUnion_of_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsOpen A ∧ P2 A) → P2 (⋃₀ 𝒜) := by
  intro h
  apply P2_sUnion
  intro A hA
  exact (h A hA).2

theorem P1_union_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P2 B → P1 (A ∪ B) := by
  intro hP1 hP2
  -- unfold the definitions of the predicates
  unfold P1 at hP1 ⊢
  unfold P2 at hP2
  intro x hx
  cases hx with
  | inl hxA =>
      -- case `x ∈ A`
      have hx_cl : x ∈ closure (interior A) := hP1 hxA
      have h_subset :
          (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono Set.subset_union_left)
      exact h_subset hx_cl
  | inr hxB =>
      -- case `x ∈ B`
      have hx_int : x ∈ interior (closure (interior B)) := hP2 hxB
      have hx_cl : x ∈ closure (interior B) := interior_subset hx_int
      have h_subset :
          (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono Set.subset_union_right)
      exact h_subset hx_cl

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} : IsClosed B → P3 A → P3 (A \ B) := by
  intro hB hP3
  -- unfold the definition of `P3`
  unfold P3 at hP3 ⊢
  intro x hxDiff
  -- split the hypothesis `x ∈ A \ B`
  have hxA    : x ∈ A        := hxDiff.1
  have hxNotB : x ∈ (Bᶜ : Set X) := hxDiff.2
  -- from `P3 A`, obtain that `x` belongs to `interior (closure A)`
  have hxIntA : x ∈ interior (closure A) := hP3 hxA
  -- define the auxiliary open set `U`
  let U : Set X := interior (closure A) ∩ Bᶜ
  have hU_open : IsOpen (U : Set X) :=
    (isOpen_interior).inter hB.isOpen_compl
  have hxU : x ∈ U := by
    dsimp [U] ; exact ⟨hxIntA, hxNotB⟩
  -- show `U ⊆ closure (A \ B)`
  have hUsubset : (U : Set X) ⊆ closure (A \ B) := by
    intro z hzU
    have hzIntA : z ∈ interior (closure A) := hzU.1
    have hzNotB : z ∈ (Bᶜ : Set X)         := hzU.2
    have hzClA  : z ∈ closure A            := interior_subset hzIntA
    -- neighbourhood criterion for the closure
    apply (mem_closure_iff).2
    intro V hV hzV
    -- refine the neighbourhood so that it is disjoint from `B`
    have hV₁_open : IsOpen (V ∩ Bᶜ : Set X) := hV.inter hB.isOpen_compl
    have hzV₁     : z ∈ V ∩ Bᶜ := ⟨hzV, hzNotB⟩
    -- since `z ∈ closure A`, this refined neighbourhood meets `A`
    have hNonempty : ((V ∩ Bᶜ) ∩ A).Nonempty :=
      (mem_closure_iff).1 hzClA _ hV₁_open hzV₁
    rcases hNonempty with ⟨y, ⟨⟨hyV, hyNotB⟩, hyA⟩⟩
    -- `y` lies in `V ∩ (A \ B)`
    exact ⟨y, ⟨hyV, ⟨hyA, hyNotB⟩⟩⟩
  -- `U` is an open nbrhood of `x` contained in the desired set
  exact (interior_maximal hUsubset hU_open) hxU