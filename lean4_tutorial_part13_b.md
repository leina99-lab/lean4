# Part 13-B: 그래프 용어와 특별한 그래프 (Graph Terminology and Special Graphs)

> **Rosen 이산수학 8판 · Section 10.1 연습문제 + Section 10.2 서론 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 13-A에서 그래프의 기본 정의와 다양한 종류(단순, 다중, 의사, 방향성, 혼합 그래프)를 배웠다. 이번 파트에서는:

1. **Section 10.1 연습문제**: 그래프 모델 구성 및 분류 문제를 Lean 4로 풀기
2. **Section 10.2 서론**: 기본 용어 — 인접, 근접, 차수, 악수 정리
3. **특별한 그래프**: 완전 그래프 $K_n$, 순환 그래프 $C_n$, 이분 그래프
4. 다양한 Lean 4 연습: 그래프 구성, 성질 증명, 모델링

---

## 1. Section 10.1 연습문제 — 그래프 모델 구성하기

### 연습 1.1 (Rosen 연습문제 1): 항공 노선 모델링

> 매일 Boston에서 Newark으로 4번의 비행, Newark에서 Boston으로 2번의 비행, Newark에서 Miami로 3번의 비행, Miami에서 Newark로 한 번의 비행, Newark에서 Detroit로 한 번의 비행, Detroit에서 Newark으로 2번의 비행, Newark에서 Washington으로 3번의 비행, Washington에서 Newark으로 2번의 비행, Washington에서 Miami로 한 번의 비행이 있다.

**질문**: 항공노선을 표현하기 위해 적절한 형태의 그래프를 설명하고 모델링하라.

**풀이**: 각 선택지별 분석

| 조건 | 방향? | 다중? | 루프? | 그래프 유형 |
|------|-------|-------|-------|-----------|
| (a) 비행 있으면 모서리 1개 | ❌ | ❌ | ❌ | **단순 그래프** |
| (b) 각 비행마다 비방향 모서리 | ❌ | ✅ | ❌ | **다중그래프** |
| (d) 출발→도착, 방향 하나씩 | ✅ | ❌ | ❌ | **단순 방향성 그래프** |
| (e) 각 비행마다 방향 모서리 | ✅ | ✅ | ✅ | **방향 다중 그래프** |

```lean
-- (a) 단순 그래프 모델
inductive City5 | Boston | Newark | Miami | Detroit | Washington
  deriving DecidableEq, Repr

open City5

-- 단순 그래프: "두 도시 사이에 비행이 존재하면 모서리"
def airlineSimple : SimpleGraph City5 where
  Adj u v := match u, v with
    | Boston, Newark | Newark, Boston => True
    | Newark, Miami | Miami, Newark => True
    | Newark, Detroit | Detroit, Newark => True
    | Newark, Washington | Washington, Newark => True
    | Washington, Miami | Miami, Washington => True
    | _, _ => False
  symm := by intro u v h; cases u <;> cases v <;> simp_all [Adj]
  loopless := by intro v; cases v <;> simp [Adj]
```

### 연습 1.2 (Rosen 연습문제 2): 고속도로 시스템

| 조건 | 그래프 유형 | 이유 |
|------|-----------|------|
| (a) 고속도로가 연결하면 모서리 1개 | **단순 그래프** | 비방향, 다중 ❌, 루프 ❌ |
| (b) 각 고속도로마다 모서리 | **다중그래프** | 비방향, 같은 두 도시 사이에 여러 고속도로 가능 |
| (c) + 순환도로 = 루프 | **의사그래프** | 비방향, 다중 ✅, 루프 ✅ |

### 연습 1.3 (Rosen 연습문제 3-9): 그래프 유형 판별

그래프를 보고 3가지 질문에 답하여 유형을 판별하는 연습이다:

| 특성 | 확인 방법 |
|------|----------|
| 방향성? | 화살표가 있으면 방향성 |
| 다중 모서리? | 같은 두 꼭짓점 사이에 2개 이상의 선 |
| 루프? | 한 꼭짓점에서 자기 자신으로의 선 |

```lean
-- 그래프 유형 판별기
inductive GraphType
  | SimpleGraph      -- 비방향, 다중 ❌, 루프 ❌
  | Multigraph       -- 비방향, 다중 ✅, 루프 ❌
  | Pseudograph      -- 비방향, 다중 ✅, 루프 ✅
  | SimpleDiGraph    -- 방향, 다중 ❌, 루프 ❌
  | DirMultigraph    -- 방향, 다중 ✅, 루프 ✅
  | MixedGraph       -- 혼합
  deriving Repr

def classifyGraph (directed : Bool) (multiEdge : Bool) (hasLoop : Bool) : GraphType :=
  match directed, multiEdge, hasLoop with
  | false, false, false => .SimpleGraph
  | false, true,  false => .Multigraph
  | false, _,     true  => .Pseudograph
  | true,  false, false => .SimpleDiGraph
  | true,  _,     _     => .DirMultigraph
  | _,     _,     _     => .MixedGraph

-- #eval classifyGraph false false false   -- SimpleGraph
-- #eval classifyGraph false true false    -- Multigraph
-- #eval classifyGraph true true true      -- DirMultigraph
```

### 연습 1.4 (Rosen 연습문제 10): 비방향성 → 단순 그래프 변환

비방향성 그래프를 단순 그래프로 변환하려면:
1. **루프** 모두 제거
2. **다중 모서리**가 있으면 하나만 남기고 나머지 제거

```lean
-- 방향성 그래프에서 비방향성 단순 그래프로 변환
-- 구조체 정의 (Part 13-A에서 가져옴)
structure SimpleDigraph (V : Type*) where
  Adj : V → V → Prop
  loopless : ∀ v, ¬ Adj v v

def toSimpleGraph (D : SimpleDigraph V) : SimpleGraph V where
  Adj u v := D.Adj u v ∨ D.Adj v u
  symm := by
    intro u v h
    rcases h with h1 | h2
    · right; exact h1
    · left; exact h2
  loopless := by
    intro v h
    rcases h with h1 | h2
    · exact D.loopless v h1
    · exact D.loopless v h2
```

### 연습 1.5 (Rosen 연습문제 11): 인접 관계의 성질

> 단순 그래프의 인접 관계는 대칭이지만 비반사적이다.

```lean
-- skeleton: 빈칸을 채워라!
theorem adj_is_symmetric (G : SimpleGraph V) :
    ∀ u v, G.Adj u v → G.Adj v u := by
  intro u v h
  exact G.⟨___⟩ h

theorem adj_is_irreflexive (G : SimpleGraph V) :
    ∀ v, ¬ G.Adj v v := by
  intro v
  exact G.⟨___⟩ v
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem adj_is_symmetric (G : SimpleGraph V) :
    ∀ u v, G.Adj u v → G.Adj v u := by
  intro u v h
  exact G.symm h

theorem adj_is_irreflexive (G : SimpleGraph V) :
    ∀ v, ¬ G.Adj v v := by
  intro v
  exact G.loopless v
```

</details>

### 연습 1.6 (Rosen 연습문제 12): 루프 있는 그래프의 관계

> 모든 꼭짓점에서 루프를 갖는 비방향성 그래프의 인접 관계는 대칭이고 **반사적**이다.

```lean
-- 루프 있는 그래프
structure LoopyGraph (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ {u v}, Adj u v → Adj v u
  all_loops : ∀ v, Adj v v    -- 모든 꼭짓점에 루프!

-- sorry로 증명하라
theorem loopy_symmetric (G : LoopyGraph V) :
    ∀ u v, G.Adj u v → G.Adj v u := by
  sorry

theorem loopy_reflexive (G : LoopyGraph V) :
    ∀ v, G.Adj v v := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem loopy_symmetric (G : LoopyGraph V) :
    ∀ u v, G.Adj u v → G.Adj v u := by
  intro u v h
  exact G.symm h

theorem loopy_reflexive (G : LoopyGraph V) :
    ∀ v, G.Adj v v := by
  intro v
  exact G.all_loops v
```

</details>

### 연습 1.7 (Rosen 연습문제 13): 교집합 그래프

> 집합의 모임 $A_1, A_2, \ldots, A_n$의 **교집합 그래프**(intersection graph)는 각 집합을 꼭짓점으로, 교집합이 공집합이 아니면 모서리로 연결한다.

```lean
-- 교집합 그래프의 정의
def intersectionGraph {n : ℕ} (sets : Fin n → Finset ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (sets i ∩ sets j).Nonempty
  symm := by
    intro i j ⟨hne, hinter⟩
    exact ⟨hne.symm, by rwa [Finset.inter_comm]⟩
  loopless := by
    intro v ⟨hne, _⟩
    exact hne rfl
```

**예 (a)**: $A_1 = \{0,2,4,6,8\}$, $A_2 = \{0,1,2,3,4\}$, $A_3 = \{1,3,5,7,9\}$, $A_4 = \{5,6,7,8,9\}$

| 쌍 | 교집합 | 모서리? |
|----|--------|--------|
| $A_1 \cap A_2$ | $\{0,2,4\}$ | ✅ |
| $A_1 \cap A_3$ | $\emptyset$ | ❌ |
| $A_1 \cap A_4$ | $\{6,8\}$ | ✅ |
| $A_2 \cap A_3$ | $\{1,3\}$ | ✅ |
| $A_2 \cap A_4$ | $\emptyset$ | ❌ |
| $A_3 \cap A_4$ | $\{5,7,9\}$ | ✅ |

```
  A₁ ● ─── ● A₂
  |         |
  A₄ ● ─── ● A₃
```

---

## 2. 특별한 그래프들

### 2.1 완전 그래프 $K_n$

**완전 그래프**(complete graph) $K_n$: 모든 서로 다른 꼭짓점 쌍이 인접하는 $n$개의 꼭짓점을 가진 단순 그래프.

모서리 수: $\binom{n}{2} = \frac{n(n-1)}{2}$

```lean
-- 완전 그래프 정의: 서로 다르면 무조건 인접!
def completeGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v
  symm := by intro u v h; exact h.symm
  loopless := by intro v h; exact h rfl
```

#### skeleton 연습: K₃ 직접 만들기

```lean
def K3 : SimpleGraph (Fin 3) where
  Adj u v := ⟨___⟩     -- 서로 다르면 인접!
  symm := by
    intro u v h
    exact h.⟨___⟩       -- 대칭성
  loopless := by
    intro v h
    exact h ⟨___⟩       -- 모순 유도
```

<details>
<summary>📝 답 보기</summary>

```lean
def K3 : SimpleGraph (Fin 3) where
  Adj u v := u ≠ v
  symm := by intro u v h; exact h.symm
  loopless := by intro v h; exact h rfl
```

</details>

### 2.2 순환 그래프 $C_n$

**순환 그래프**(cycle graph) $C_n$ ($n \geq 3$): 꼭짓점 $0, 1, \ldots, n-1$이 원형으로 연결된 그래프.

```
C₃ (삼각형):    C₄ (사각형):    C₅ (오각형):
    0               0 ─── 1         0
   / \              |     |       /   \
  1 ─ 2             3 ─── 2     1     4
                                 \   /
                                  2─3
```

```lean
-- 순환 그래프 C₄ 정의
def C4 : SimpleGraph (Fin 4) where
  Adj u v :=
    (u.val + 1) % 4 = v.val ∨ (v.val + 1) % 4 = u.val
  symm := by
    intro u v h
    rcases h with h1 | h2
    · right; exact h1
    · left; exact h2
  loopless := by
    intro v h; rcases h with h1 | h2 <;> omega
```

#### sorry 연습: C₅ 정의하기

```lean
def C5 : SimpleGraph (Fin 5) where
  Adj u v := sorry
  symm := by sorry
  loopless := by sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
def C5 : SimpleGraph (Fin 5) where
  Adj u v :=
    (u.val + 1) % 5 = v.val ∨ (v.val + 1) % 5 = u.val
  symm := by
    intro u v h
    rcases h with h1 | h2
    · right; exact h1
    · left; exact h2
  loopless := by
    intro v h; rcases h with h1 | h2 <;> omega
```

</details>

### 2.3 이분 그래프(bipartite graph)

**이분 그래프**: 꼭짓점 집합을 두 개의 서로소인 부분집합 $V_1$, $V_2$로 나눌 수 있어서, 모든 모서리가 $V_1$의 꼭짓점과 $V_2$의 꼭짓점을 연결하는 그래프.

**직관**: 꼭짓점을 **2가지 색**으로 칠할 수 있고, **같은 색끼리는 인접하지 않는** 그래프!

```lean
-- 이분 그래프 성질
def isBipartite (G : SimpleGraph V) (color : V → Bool) : Prop :=
  ∀ u v, G.Adj u v → color u ≠ color v

-- C₄는 이분 그래프 (색칠: 0→true, 1→false, 2→true, 3→false)
-- K₃는 이분 그래프가 아니다! (3개를 2색으로 칠하면 같은 색 인접 발생)
```

### 2.4 보 그래프(complement graph)

**보 그래프**(complement) $\overline{G}$: $G$에서 인접하지 않는 서로 다른 쌍을 인접하게 만든 그래프.

```lean
def complementGraph (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ¬ G.Adj u v
  symm := by
    intro u v ⟨hne, hnadj⟩
    exact ⟨hne.symm, fun h => hnadj (G.symm h)⟩
  loopless := by
    intro v ⟨hne, _⟩; exact hne rfl
```

#### sorry 연습: 보 그래프의 보 = 원래 그래프

```lean
theorem complement_complement (G : SimpleGraph V) (u v : V) :
    (complementGraph (complementGraph G)).Adj u v ↔ G.Adj u v := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem complement_complement (G : SimpleGraph V) (u v : V) :
    (complementGraph (complementGraph G)).Adj u v ↔ G.Adj u v := by
  simp [complementGraph]
  constructor
  · intro ⟨hne, hnn⟩
    by_contra h
    exact hnn ⟨hne, h⟩
  · intro h
    constructor
    · intro heq; subst heq; exact G.loopless v h
    · intro ⟨_, hng⟩; exact hng h
```

</details>

### 2.5 부분 그래프(subgraph)

**부분 그래프**(subgraph): $H$의 모든 꼭짓점이 $G$의 꼭짓점이고, $H$의 모든 모서리가 $G$의 모서리.

```lean
def isSubgraph (H G : SimpleGraph V) : Prop :=
  ∀ u v, H.Adj u v → G.Adj u v

-- sorry 연습
theorem subgraph_adj (H G : SimpleGraph V) (hsub : isSubgraph H G)
    (u v : V) (h : H.Adj u v) : G.Adj u v := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem subgraph_adj (H G : SimpleGraph V) (hsub : isSubgraph H G)
    (u v : V) (h : H.Adj u v) : G.Adj u v := by
  exact hsub u v h
```

</details>

---

## 3. Section 10.2 서론: 그래프 이론의 기본 용어

### 3.1 인접(adjacency)과 근접(incidence)

비방향성 그래프에서 모서리 $e = \{u, v\}$가 있으면:
- $u$와 $v$는 **인접한다**(adjacent) = **이웃**(neighbors)
- $e$는 $u$와 $v$에 **근접한다**(incident)
- $u$와 $v$는 $e$의 **끝점**(endpoints)

### 3.2 차수(degree)

꼭짓점 $v$의 **차수**(degree) $\deg(v)$는 $v$에 인접한 꼭짓점의 수 (= $v$에 근접한 모서리의 수).

- 고립점(isolated vertex): 차수 0인 꼭짓점
- 현수점(pendant vertex): 차수 1인 꼭짓점

### 3.3 악수 정리(Handshaking Theorem)

> **악수 정리**: $\sum_{v \in V} \deg(v) = 2|E|$

**왜?** 각 모서리 {u,v}는 u의 차수에 1, v의 차수에 1을 기여하므로, 합계 = 2 × 모서리 수.

**따름정리**: 모든 그래프에서 **홀수 차수를 가진 꼭짓점의 수는 짝수**이다!

```lean
-- 악수 정리의 결과: 홀수 차수 꼭짓점의 수는 짝수
-- 증명 스케치:
-- 모든 차수의 합 = 2|E| (짝수)
-- 짝수 차수 꼭짓점의 합 = 짝수
-- 따라서 홀수 차수 꼭짓점의 합 = 짝수
-- 홀수들의 합이 짝수 → 홀수의 개수가 짝수!
```

---

## 4. 핵심 요약

1. **그래프 모델링**: 상황 분석 → 3가지 질문 → 적절한 유형 선택.
2. **단순 그래프의 인접 관계**: **대칭적** + **비반사적**.
3. **루프 있는 그래프의 인접 관계**: **대칭적** + **반사적**.
4. **교집합 그래프**: 집합들 간 교집합 ≠ ∅이면 모서리.
5. **완전 그래프** $K_n$: `Adj u v := u ≠ v`.
6. **순환 그래프** $C_n$: 원형 연결, `(u+1)%n = v` 또는 `(v+1)%n = u`.
7. **이분 그래프**: 2색 칠하기 가능, 같은 색 인접 없음.
8. **보 그래프** $\overline{G}$: 인접 ↔ 비인접 반전, $\overline{\overline{G}} = G$.
9. **악수 정리**: $\sum \deg(v) = 2|E|$ → 홀수 차수 꼭짓점 수는 짝수.
10. **부분 그래프**: 원래 그래프의 부분집합으로 구성.

---

## 5. 사용된 Lean 4 전술 정리

| 전술 | 용도 | 예시 |
|------|------|------|
| `SimpleGraph V` | 단순 그래프 타입 | `def G : SimpleGraph (Fin n)` |
| `G.symm` | 인접 대칭성 | `G.symm h` |
| `G.loopless` | 루프 없음 | `G.loopless v` |
| `constructor` | ∧, ↔ 분리 | 양방향 증명 |
| `by_contra` | 귀류법 | 모순 유도 |
| `rcases` | 패턴 분해 | Or/And 분해 |
| `omega` | 산술 자동증명 | 나머지 연산 처리 |
| `simp` | 정의 펼침 | 복잡한 정의 단순화 |
| `rwa` | rw + assumption | 치환 후 가설 사용 |
| `Finset.inter_comm` | 교집합 교환 | $A \cap B = B \cap A$ |

---

> **다음 파트 예고**: Part 13-C에서는 Section 10.2를 본격적으로 다룬다. **차수**(degree)의 상세한 증명, **악수 정리**(Handshaking Theorem)의 Lean 4 구현, **완전 이분 그래프** $K_{m,n}$, **바퀴 그래프** $W_n$, **n-큐브** $Q_n$, **정규 그래프**(regular graph), 그리고 그래프의 **동형**(isomorphism)을 Lean 4로 구현한다!
