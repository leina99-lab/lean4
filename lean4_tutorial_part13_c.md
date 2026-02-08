# Part 13-C: 그래프 용어와 특별한 그래프 (1) — 기본 용어, 차수, 악수 정리

> **Rosen 이산수학 8판 · Section 10.2 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 13-A에서는 **그래프**(graph)가 무엇인지, 어떤 종류가 있는지 큰 그림을 그렸다. Part 13-B에서는 Section 10.1 연습문제와 몇 가지 특별한 그래프를 맛보았다. 이번 Part 13-C에서는 그래프 이론의 **핵심 용어들**을 본격적으로 배운다.

이 파트에서 다루는 내용은 다음과 같다:

1. **인접**(adjacent)과 **붙어있다**(incident)의 정확한 뜻
2. **이웃**(neighbor)과 **이웃 집합**(neighborhood) N(v)
3. **차수**(degree) — 꼭지점에 연결된 모서리 수
4. **고립**(isolated) 꼭지점과 **늘어진**(pendant) 꼭지점
5. **악수 정리**(handshaking theorem): 차수의 합 = 모서리 수의 2배
6. **홀수 차수 정리**: 홀수 차수 꼭지점의 개수는 짝수
7. **방향성 그래프**(digraph)에서의 **입력차수**(in-degree)와 **출력차수**(out-degree)
8. **특수한 단순 그래프**: 완전 그래프 Kₙ, 사이클 Cₙ, 휠 Wₙ, n-큐브 Qₙ
9. Lean 4에서 이 모든 것을 `structure`와 `Finset`으로 표현하고 증명하기

> **핵심 비유**: 그래프 이론의 용어를 배우는 것은 마치 새로운 도시의 지도를 읽는 법을 배우는 것과 같다. "교차로"(꼭지점), "도로"(모서리), "교차로에서 나가는 도로 수"(차수)를 알면 도시 전체를 파악할 수 있다!

---

## 1. 기본 용어들 (Section 10.2.2)

### 1.1 인접과 붙어있다

비방향성 그래프에서 가장 기본이 되는 용어부터 시작하자.

> **정의 1** (Rosen): 비방향성 그래프 G에서 두 꼭지점 u와 v가 G의 모서리의 끝점이라면 u와 v는 **인접한다**(adjacent 또는 neighbor, 이웃)고 한다. e가 {u, v}와 관련되면 '모서리 e는 꼭지점 u와 v에 **붙어있다**(incident)'고 한다. 모서리 e는 u와 v를 **연결**(connect)한다고도 말한다. 꼭지점 u와 v는 {u, v}와 연관된 모서리의 **끝점**(end point)들이라고 부른다.

이것을 일상 언어로 풀어보자:

- **인접하다**: 두 사람이 직접 악수할 수 있으면 "인접"이다. 중간에 다른 사람을 거치지 않고 바로 연결된 것이다.
- **붙어있다**: 모서리(도로)가 꼭지점(교차로)에 물리적으로 연결되어 있다는 뜻이다. "서울-부산 고속도로"는 "서울"이라는 교차로와 "부산"이라는 교차로에 붙어있다.
- **연결하다**: 모서리가 두 꼭지점을 이어준다.
- **끝점**: 모서리의 양쪽 끝에 있는 꼭지점이다.

```lean
-- Lean 4에서 단순 그래프의 인접 관계
-- Mathlib의 SimpleGraph는 Adj 필드로 인접을 정의한다

structure SimpleGraph' (V : Type) where
  Adj : V → V → Prop          -- u와 v가 인접한가?
  symm : ∀ u v, Adj u v → Adj v u   -- 비방향: u~v이면 v~u
  loopless : ∀ v, ¬ Adj v v         -- 루프 없음: 자기 자신과 인접 ✗

-- 구체적 예: 꼭지점 {a, b, c, d, e, f, g}에 대한 그래프 G (Rosen 그림 1)
-- 모서리: {a,b}, {a,e}, {a,f}, {b,c}, {b,e}, {b,f}, {c,d}, {c,e}, {c,f}, {d,e}

inductive V7 | a | b | c | d | e | f | g
  deriving DecidableEq, Repr

open V7

def G_fig1 : SimpleGraph' V7 where
  Adj := fun u v => match u, v with
    | a, b => True | b, a => True
    | a, e => True | e, a => True
    | a, f => True | f, a => True
    | b, c => True | c, b => True
    | b, e => True | e, b => True
    | b, f => True | f, b => True
    | c, d => True | d, c => True  -- 기타 c,e / c,f / d,e도 추가 가능
    | c, e => True | e, c => True
    | c, f => True | f, c => True
    | d, e => True | e, d => True
    | _, _ => False
  symm := by intros u v h; revert h; cases u <;> cases v <;> simp_all
  loopless := by intro v; cases v <;> simp_all
```

**핵심 포인트**: `Adj u v`가 `True`이면 u와 v는 인접한다. `symm` 필드가 양방향성을, `loopless`가 루프 없음을 보장한다.

### 1.2 이웃과 이웃 집합

> **정의 2** (Rosen): 그래프 G = (V, E)의 꼭지점 v의 모든 **이웃**(neighbor)들의 집합을 N(v)로 표기하고 v의 **이웃**(neighborhood)이라한다. A가 V의 부분집합이라면 N(A)는 A 안의 각각의 꼭지점들에 인접한 모든 꼭지점들의 집합이다. 그러므로 N(A) = ⋃_{v∈A} N(v)이다.

쉽게 말하면:

- N(v) = "v와 직접 연결된 모든 꼭지점의 집합"
- N(A) = "A에 속한 어떤 꼭지점과라도 직접 연결된 모든 꼭지점의 집합"

**비유**: SNS에서 N(나) = "내 친구 목록", N({나, 철수}) = "나의 친구 목록 ∪ 철수의 친구 목록"

```lean
-- 이웃 집합을 Finset으로 표현 (유한 그래프)
-- 꼭지점이 Fin n일 때의 이웃 집합
def neighbors (adj : Fin n → Fin n → Bool) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => adj v u)

-- 예: 그래프 G에서 각 꼭지점의 이웃 (Rosen 예제 1)
-- N(a) = {b, f}, N(b) = {a, c, e, f}, N(c) = {b, d, e, f}
-- N(d) = {c, e}, N(e) = {a, b, c, e}, N(f) = {a, b, c, e}
-- N(g) = ∅  (g는 아무 꼭지점과도 연결되지 않았다!)
```

### 1.3 차수 — 꼭지점의 "인기도"

> **정의 3** (Rosen): 비방향성 그래프에서 꼭지점의 **차수**(degree)는 그 꼭지점에 붙어 있는 모서리들의 개수인데, 꼭지점이 하나의 루프를 가지는 경우 차수는 2를 더하면 된다. 꼭지점 v의 차수는 deg(v)로 표기한다.

차수는 직관적으로 **"그 꼭지점이 얼마나 많은 연결을 가지고 있는가"** 를 나타낸다.

- deg(v) = |N(v)| (단순 그래프에서 — 루프와 다중 모서리가 없을 때)
- 루프가 있으면 루프 하나당 차수에 2를 더한다 (루프는 같은 꼭지점에서 시작하고 끝나므로)

**비유**: 파티에서 한 사람의 "차수"는 그 사람이 악수한 사람의 수이다!

```lean
-- 단순 그래프에서 차수 = 이웃의 수
def degree (adj : Fin n → Fin n → Bool) (v : Fin n) : ℕ :=
  (neighbors adj v).card

-- Rosen 예제 1의 그래프 G에서 각 꼭지점의 차수:
-- deg(a) = 2, deg(b) = deg(c) = deg(f) = 4, deg(d) = 1, deg(e) = 3, deg(g) = 0
```

### 1.4 특별한 꼭지점들: 고립과 늘어진

차수가 특수한 값을 가지는 꼭지점들에는 특별한 이름이 붙어 있다:

- **고립된 꼭지점**(isolated vertex): deg(v) = 0인 꼭지점. 어떤 다른 꼭지점과도 인접하지 않는다.
  - 예: 그림 1의 그래프 G에서 꼭지점 g는 고립되었다
  - 비유: 파티에 왔지만 아무와도 악수하지 않은 사람
  
- **늘어진 꼭지점**(pendant vertex): deg(v) = 1인 꼭지점. 정확히 하나의 다른 꼭지점과 인접한다.
  - 예: 그림 1의 그래프 G에서 꼭지점 d는 늘어진 꼭지점이다 (c하고만 연결)
  - 비유: 나무의 끝 가지에 매달린 잎사귀 — 하나의 가지에만 붙어 있다

```lean
-- 특별한 꼭지점 판별
def isIsolated (adj : Fin n → Fin n → Bool) (v : Fin n) : Prop :=
  degree adj v = 0

def isPendant (adj : Fin n → Fin n → Bool) (v : Fin n) : Prop :=
  degree adj v = 1
```

---

## 2. 악수 정리 (Handshaking Theorem)

### 2.1 직관적 이해

파티에서 사람들이 악수를 한다고 상상하자. 각 악수(=모서리)는 정확히 **두 사람**(=두 꼭지점)이 참여한다. 따라서:

- 각 모서리는 정확히 2의 차수를 기여한다 (양쪽 끝점에 각각 1씩)
- 모든 차수를 합하면, 각 모서리가 2번씩 세어진다
- 결론: **차수의 합 = 모서리 수 × 2**

이것이 바로 악수 정리이다!

### 2.2 공식 서술

> **정리 1 (악수 정리)**: G = (V, E)를 m개의 모서리를 갖는 비방향성 그래프라 하자. 그러면
>
> 2m = Σ_{v∈V} deg(v)
>
> (주의: 다중 모서리와 루프를 갖는 그래프에서도 같은 결과가 적용된다.)

**증명의 핵심 아이디어**: 각 모서리 {u, v}는 deg(u)에 1을, deg(v)에 1을 기여한다. 따라서 총 합에 2를 기여한다. m개의 모서리가 각각 2를 기여하므로 합은 2m이다.

```lean
-- 악수 정리의 Lean 4 표현 (유한 그래프)
-- 핵심: 차수의 합 = 2 × 모서리 수

-- 인접 행렬로 그래프 표현
def adjBool7 : Fin 7 → Fin 7 → Bool
  | 0, 1 => true | 1, 0 => true  -- a-b
  | 0, 4 => true | 4, 0 => true  -- a-e
  | 0, 5 => true | 5, 0 => true  -- a-f
  | 1, 2 => true | 2, 1 => true  -- b-c
  | 1, 4 => true | 4, 1 => true  -- b-e
  | 1, 5 => true | 5, 1 => true  -- b-f
  | 2, 3 => true | 3, 2 => true  -- c-d  (그래프에 따라 c-e, c-f, d-e 등 추가)
  | 2, 4 => true | 4, 2 => true  -- c-e
  | 2, 5 => true | 5, 2 => true  -- c-f
  | 3, 4 => true | 4, 3 => true  -- d-e
  | _, _ => false

-- 차수 합 계산
def sumDegrees (adj : Fin n → Fin n → Bool) : ℕ :=
  (Finset.univ.sum fun v => degree adj v)

-- 모서리 수 계산 (각 모서리를 한 번만 센다: i < j인 쌍)
def countEdges (adj : Fin n → Fin n → Bool) : ℕ :=
  (Finset.univ.sum fun i =>
    ((Finset.univ.filter fun j => i < j ∧ adj i j).card))

-- 악수 정리: sumDegrees = 2 * countEdges
-- 이것은 모든 유한 단순 그래프에서 성립한다!
-- #eval sumDegrees adjBool7    -- 결과: 20
-- #eval countEdges adjBool7    -- 결과: 10
-- 20 = 2 × 10 ✓
```

### 2.3 예제 3 (Rosen)

> 각각의 차수가 6인 10개의 꼭지점을 갖는 그래프에는 몇 개의 모서리가 존재하는가?

**풀이**: 악수 정리에 의해 2m = Σ deg(v) = 6 × 10 = 60. 따라서 m = 30이다.

```lean
-- 악수 정리 적용 예
example : 6 * 10 / 2 = 30 := by norm_num

-- 일반적 형태: n개의 꼭지점이 모두 차수 k이면 모서리 수 = n*k/2
-- 이때 n*k가 짝수여야 한다! (왜? 2m = n*k이므로 n*k는 짝수)
```

### 2.4 홀수 차수 꼭지점의 개수는 짝수

악수 정리에서 중요한 결론을 하나 더 이끌어낼 수 있다.

> **정리 2**: 비방향성 그래프에서 홀수 차수의 꼭지점의 개수는 짝수여야 한다.

**증명**: 비방향성 그래프 G = (V, E)에서, V₁은 짝수 차수 꼭지점들의 집합이고 V₂는 홀수 차수 꼭지점들의 집합이라 하자.

2m = Σ_{v∈V} deg(v) = Σ_{v∈V₁} deg(v) + Σ_{v∈V₂} deg(v)

v ∈ V₁에 대해 deg(v)는 짝수이기 때문에 마지막 수식 오른쪽 부분의 첫 항은 짝수이다. 게다가 합이 2m이므로 마지막 수식 오른쪽 부분의 두 항의 합은 짝수이므로 합의 두 번째 항도 또한 짝수이다. 이 합의 모든 항들은 홀수이기 때문에 그런 항들은 짝수 개가 있어야 한다. 그러므로 홀수 차수의 꼭지점들의 수는 짝수 개다. ◁

```lean
-- 정리 2의 핵심 아이디어를 Lean 4로 표현
-- V₁ = 짝수 차수 꼭지점 집합, V₂ = 홀수 차수 꼭지점 집합
-- Σ V₂의 각 항은 홀수 → 짝수가 되려면 항의 수가 짝수여야 함

-- 간단한 보조 정리: 홀수들의 합이 짝수이면 항의 수가 짝수
lemma even_count_of_odd_sum {l : List ℕ}
  (h_odd : ∀ x ∈ l, ¬ Even x) (h_even : Even l.sum) :
  Even l.length := by
  sorry  -- 이것은 귀납법으로 증명 가능

-- 구체적 검증: 그래프 G에서
-- deg = [2, 4, 4, 1, 3, 4, 0] (각 꼭지점 a~g의 차수)
-- 홀수 차수: d(차수1), e(차수3) → 2개 (짝수!) ✓
```

**직관적 이해**: 모든 사람이 악수한 횟수의 합은 항상 짝수이다 (각 악수에 2명이 참여하니까). 이 합을 "짝수 횟수 악수한 사람" + "홀수 횟수 악수한 사람"으로 나누면, 첫 부분은 짝수이므로 두 번째 부분도 짝수여야 한다. 홀수의 합이 짝수가 되려면 항의 개수가 짝수여야 한다!

---

## 3. 방향성 그래프에서의 차수

### 3.1 인접의 방향

비방향성 그래프에서는 "u와 v가 인접"이면 양방향이었다. 방향성 그래프에서는 **방향이 구분**된다.

> **정의 4** (Rosen): (u, v)가 방향성 모서리를 갖는 그래프 G의 모서리일 때 방향성 모서리 u는 v에 **인접한다**(adjacent to)라고 하고 v는 u로부터 **인접된다**(adjacent from)라고 한다. 꼭지점 u는 (u, v)의 **시작 꼭지점**(initial vertex)이라 하고 v는 (u, v)의 **종료**(terminal) 혹은 **끝 꼭지점**(end vertex)이라 한다. 루프의 시작 꼭지점과 끝 꼭지점은 같다.

**비유**: 트위터에서 "A가 B를 팔로우한다"는 A→B 방향 모서리이다. A는 시작 꼭지점, B는 끝 꼭지점이다. "A가 B에 인접한다"는 맞지만, "B가 A에 인접한다"는 A가 B를 팔로우한다는 것과 다르다!

### 3.2 입력차수와 출력차수

> **정의 5** (Rosen): 방향성 모서리를 갖는 그래프에서 꼭지점 v의 **입력차수**(in-degree)는 deg⁻(v)로 표기하고 종료 꼭지점으로서 v가 갖는 모서리의 수이다. v의 **출력차수**(out-degree)는 deg⁺(v)로 표기하고 시작 꼭지점으로서 v가 갖는 모서리의 수이다(한 꼭지점에서 루프는 그 꼭지점의 입력차수와 출력차수 둘 다에 1씩을 나타낸다).

쉽게 말하면:
- **입력차수** deg⁻(v) = "v로 들어오는 화살표 수" (몇 명이 나를 팔로우하는가?)
- **출력차수** deg⁺(v) = "v에서 나가는 화살표 수" (내가 몇 명을 팔로우하는가?)

```lean
-- 방향성 그래프 구조
structure Digraph (V : Type) where
  edge : V → V → Prop

-- 입력차수와 출력차수 (유한 그래프)
def inDegree (edge : Fin n → Fin n → Bool) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun u => edge u v).card

def outDegree (edge : Fin n → Fin n → Bool) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun u => edge v u).card
```

### 3.3 예제 4 (Rosen): 방향성 그래프 G의 차수 계산

그림 2의 방향성 그래프 G에서 각 꼭지점의 입력차수와 출력차수를 구하라.

**풀이**:
- G의 들어오는 차수(in-degree): deg⁻(a) = 2, deg⁻(b) = 2, deg⁻(c) = 3, deg⁻(d) = 2, deg⁻(e) = 3, deg⁻(f) = 0
- G의 출력차수(out-degree): deg⁺(a) = 4, deg⁺(b) = 1, deg⁺(c) = 2, deg⁺(d) = 2, deg⁺(e) = 3, deg⁺(f) = 0

```lean
-- 방향성 그래프 예제 (6개 꼭지점: a=0, b=1, c=2, d=3, e=4, f=5)
def digraph_fig2 : Fin 6 → Fin 6 → Bool
  | 0, 0 => true  -- a→a (루프)
  | 0, 1 => true  -- a→b
  | 0, 2 => true  -- a→c
  | 0, 3 => true  -- a→d
  | 1, 4 => true  -- b→e
  | 2, 1 => true  -- c→b
  | 2, 4 => true  -- c→e
  | 3, 2 => true  -- d→c
  | 3, 4 => true  -- d→e
  | 4, 0 => true  -- e→a
  | 4, 2 => true  -- e→c
  | 4, 3 => true  -- e→d
  | _, _ => false

-- #eval (List.finRange 6).map fun v => (inDegree digraph_fig2 v, outDegree digraph_fig2 v)
-- 결과: [(2,4), (2,1), (3,2), (2,2), (3,3), (0,0)]
```

### 3.4 정리 3: 방향성 그래프의 차수 정리

> **정리 3**: 그래프 G = (V, E)가 방향성 모서리를 갖는다 하자. 그러면 다음과 같다.
>
> Σ_{v∈V} deg⁻(v) = Σ_{v∈V} deg⁺(v) = |E|

**증명 아이디어**: 각 모서리 (u, v)는 u의 출력차수에 1을, v의 입력차수에 1을 기여한다. 따라서 입력차수의 합과 출력차수의 합은 모두 모서리의 수와 같다.

```lean
-- 정리 3 검증
-- #eval (List.finRange 6).map (inDegree digraph_fig2) |>.sum   -- 12
-- #eval (List.finRange 6).map (outDegree digraph_fig2) |>.sum  -- 12
-- 모서리 수 = 12 ✓
```

### 3.5 비방향성 근저 그래프

방향성 그래프에서 모서리의 방향을 무시해서 생긴 비방향성 그래프를 **비방향성 근저 그래프**(underlying undirected graph)라 부른다. 방향성 모서리를 갖는 그래프와 그 비방향성 근저 그래프는 같은 수의 모서리를 가진다.

```lean
-- 방향성 → 비방향성 변환
def underlying (edge : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  fun i j => edge i j || edge j i
```

---

## 4. 단순 그래프의 특수한 예 (Section 10.2.3)

그래프 이론에서 자주 등장하는 몇 가지 중요한 그래프 패턴을 소개한다. 이 그래프들은 다른 그래프의 "빌딩 블록"처럼 사용되며, 많은 정리에서 핵심적인 역할을 한다.

### 4.1 완전 그래프 Kₙ

> **예제 5** (Rosen): 꼭지점 n개를 갖는 **완전 그래프**(complete graph)는 Kₙ으로 표기한다. 완전 그래프는 모든 서로 다른 꼭지점들의 각 쌍 사이에 정확히 하나의 모서리만을 갖는 단순 그래프이다.

쉽게 말하면: **모든 사람이 다른 모든 사람과 악수**한 그래프이다!

- K₁: 꼭지점 1개, 모서리 0개 (혼자)
- K₂: 꼭지점 2개, 모서리 1개 (두 사람이 악수)
- K₃: 꼭지점 3개, 모서리 3개 (삼각형)
- K₄: 꼭지점 4개, 모서리 6개
- K₅: 꼭지점 5개, 모서리 10개

일반적으로 Kₙ의 모서리 수 = n(n-1)/2 (= C(n, 2))

```lean
-- 완전 그래프 Kₙ: 모든 서로 다른 꼭지점이 인접
def completeGraph (n : ℕ) : Fin n → Fin n → Bool :=
  fun i j => i != j

-- 완전 그래프의 성질
-- 모든 꼭지점의 차수 = n - 1
-- 모서리 수 = n(n-1)/2
-- 악수 정리 검증: n(n-1) = Σ deg(v) = n × (n-1) ✓

-- 예: K₅의 차수와 모서리 수
-- #eval degree (completeGraph 5) ⟨0, by omega⟩  -- 4
-- #eval countEdges (completeGraph 5)             -- 10
-- 10 = 5 × 4 / 2 ✓
```

단순 그래프 중 모서리로 연결되지지 않은 적어도 한 쌍의 꼭지점들을 가지는 그래프는 **불완전 그래프**(noncomplete graph)라고 부른다.

### 4.2 사이클 Cₙ

> **예제 6** (Rosen): **사이클**(cycle) Cₙ (n ≥ 3)은 n개의 꼭지점들 v₁, v₂, ..., vₙ과 모서리 {v₁, v₂}, {v₂, v₃}, ..., {v_{n-1}, vₙ} 그리고 {vₙ, v₁}으로 구성한다.

사이클은 **원형으로 연결**된 그래프이다.

- C₃: 삼각형 (모든 꼭지점 차수 2)
- C₄: 정사각형
- C₅: 오각형
- C₆: 육각형

**핵심 성질**: Cₙ의 모든 꼭지점의 차수는 2이다. 모서리 수는 n이다.

```lean
-- 사이클 그래프 Cₙ: 각 꼭지점이 다음 및 이전 꼭지점과 인접
def cycleGraph (n : ℕ) (h : n ≥ 3) : Fin n → Fin n → Bool :=
  fun i j =>
    (j.val == (i.val + 1) % n) || (i.val == (j.val + 1) % n)

-- 사이클의 차수: 모든 꼭지점이 차수 2
-- 악수 정리: 2n = Σ deg(v) = n × 2 = 2n ✓
```

### 4.3 휠 Wₙ

> **예제 7** (Rosen): n ≥ 3인 **휠**(wheel)의 중간에 꼭지점 하나를 추가하고 이 새 꼭지점과 의 모든 꼭지점들을 새 모서리들로 연결하면 **휠** Wₙ을 얻는다.

**비유**: 자전거 바퀴를 생각하자! 바깥쪽 테두리가 사이클 Cₙ이고, 중심축(허브)이 추가된 꼭지점이다. 허브에서 테두리의 모든 꼭지점으로 바큇살이 나간다.

- Wₙ = Cₙ + 중심 꼭지점 + n개의 바큇살
- 꼭지점 수: n + 1
- 모서리 수: 2n (사이클의 n개 + 바큇살 n개)
- 테두리 꼭지점의 차수: 3 (왼쪽 이웃 + 오른쪽 이웃 + 중심)
- 중심 꼭지점의 차수: n

```lean
-- 휠 그래프 Wₙ: 사이클 Cₙ + 중심 꼭지점 (인덱스 n)
-- 총 꼭지점: n+1개 (Fin (n+1)에서 n번이 중심)
def wheelGraph (n : ℕ) (h : n ≥ 3) : Fin (n + 1) → Fin (n + 1) → Bool :=
  fun i j =>
    -- 중심(n)과 테두리 꼭지점 사이
    (i.val == n && j.val < n) ||
    (j.val == n && i.val < n) ||
    -- 테두리: 사이클 관계 (i, j 모두 < n일 때)
    (i.val < n && j.val < n &&
      ((j.val == (i.val + 1) % n) || (i.val == (j.val + 1) % n)))
```

### 4.4 n-큐브 Qₙ

> **예제 8** (Rosen): **n-큐브**(n-dimensional hypercube, n-cube) Qₙ은 길이 n의 2ⁿ 비트 스트링(문자열, string)을 나타내는 꼭지점들을 갖는 그래프이다. 두 꼭지점들이 인접해 있다면 이들이 나타내는 비트 스트링은 정확히 한 비트의 위치에서만 다르다.

**비유**: 
- Q₁: 비트 0과 1 — 두 꼭지점, 하나의 모서리 (선분)
- Q₂: 비트 00, 01, 10, 11 — 네 꼭지점 (정사각형)
- Q₃: 비트 000, 001, ..., 111 — 여덟 꼭지점 (정육면체!)

n-큐브는 컴퓨터 과학에서 **매우 중요**하다. 병렬 컴퓨팅의 프로세서 연결망(하이퍼큐브 네트워크)에 사용된다.

**핵심 성질**:
- 꼭지점 수: 2ⁿ
- 모서리 수: n × 2^(n-1)
- 모든 꼭지점의 차수: n (각 비트 위치마다 하나의 이웃)

```lean
-- n-큐브: 해밍 거리가 1인 비트 스트링이 인접
-- 비트 스트링 = Fin n → Bool (길이 n의 비트 배열)
-- 해밍 거리 = 다른 비트의 수

def hammingDist (a b : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => a i != b i).card

-- Qₙ: 해밍 거리가 정확히 1인 두 비트 스트링이 인접
def hypercubeAdj (n : ℕ) (a b : Fin n → Bool) : Prop :=
  hammingDist a b = 1

-- Q₃ 구체적 예:
-- 000-001, 000-010, 000-100 (한 비트만 다른 것들)
-- 이것은 정육면체의 모서리 구조와 같다!
```

### 4.5 (n+1)-큐브 구성법

Rosen은 (n+1)-큐브 Q_{n+1}을 두 개의 n-큐브 Qₙ으로 쉽게 만들어 보일 수 있다고 설명한다. Qₙ의 하나는 모든 꼭지점의 레이블 앞에 0을 붙이고, 다른 Qₙ의 모든 꼭지점의 레이블 앞에 1을 붙이고, 첫 비트에서만 다른 레이블을 갖는 두 꼭지점을 연결하는 모서리를 추가한다.

```lean
-- 재귀적 구성: Q_{n+1} = 2 × Qₙ + 연결 모서리
-- 아래쪽 Qₙ: 0으로 시작하는 비트 스트링
-- 위쪽 Qₙ: 1로 시작하는 비트 스트링
-- 연결: 첫 비트만 다른 두 꼭지점을 모서리로 연결
```

---

## 5. 정규 그래프

단순 그래프의 모든 꼭지점이 같은 차수를 갖는다면, 이 단순 그래프는 **정규**(regular) 하다고 한다. 정규 그래프의 모든 꼭지점이 차수 n을 가진다면 **n-정규**라고 한다.

**예시**:
- Kₙ은 (n-1)-정규이다 (모든 꼭지점이 n-1개의 이웃)
- Cₙ은 2-정규이다 (모든 꼭지점이 차수 2)
- Q₃은 3-정규이다 (모든 꼭지점이 차수 3)

```lean
-- 정규 그래프 판정
def isRegular (adj : Fin n → Fin n → Bool) (k : ℕ) : Prop :=
  ∀ v : Fin n, degree adj v = k

-- 완전 그래프 Kₙ은 (n-1)-정규
theorem complete_is_regular (n : ℕ) (h : n ≥ 1) :
  isRegular (completeGraph n) (n - 1) := by
  sorry  -- 모든 꼭지점이 자신을 제외한 n-1개와 인접

-- n-정규 그래프의 모서리 수 (악수 정리 적용)
-- 2m = n × k (n은 꼭지점 수, k는 차수)
-- 따라서 m = n × k / 2 (n*k가 짝수여야 함!)
```

---

## 6. 차수 수열

그래프의 **차수 수열**(degree sequence)은 증가하지 않는 순서로 그래프의 꼭지점들의 차수를 순서화하는 것이다. 예를 들어 이 절의 예제 1의 그래프에서 차수 순서는 4, 4, 4, 3, 2, 1, 0이다.

단순 그래프에서 차수 수열(degree sequence)이 존재한다면 그 수열 d₁, d₂, ..., dₙ을 **그래픽**(graphic)이라 한다.

```lean
-- 차수 수열: 차수를 내림차순으로 정렬
def degreeSequence (adj : Fin n → Fin n → Bool) : List ℕ :=
  ((List.finRange n).map (degree adj)).mergeSort (· ≥ ·)

-- 예: adjBool7의 차수 수열
-- 차수: [2, 4, 4, 1, 3, 4, 0]
-- 정렬: [4, 4, 4, 3, 2, 1, 0]
```

---

## 7. 연습 문제 — 레벨 1: 괄호 채우기

### 연습 7.1: 차수와 이웃 구하기 (Rosen 연습문제 1)

다음 그래프 G에서 각 꼭지점의 차수와 이웃을 구하라.

꼭지점: {a, b, c, d, e, f}, 모서리: {a,b}, {a,e}, {b,c}, {b,e}, {b,f}, {c,d}, {c,f}, {d,e}, {e,f}

```lean
-- 인접 행렬 정의 (6개 꼭지점: a=0, b=1, c=2, d=3, e=4, f=5)
def adj_7_1 : Fin 6 → Fin 6 → Bool
  | 0, 1 => true | 1, 0 => true  -- a-b
  | 0, 4 => true | 4, 0 => true  -- a-e
  | 1, 2 => true | 2, 1 => true  -- b-c
  | 1, 4 => true | 4, 1 => true  -- b-e
  | 1, 5 => true | 5, 1 => true  -- b-f
  | 2, 3 => true | 3, 2 => true  -- c-d
  | 2, 5 => true | 5, 2 => true  -- c-f
  | 3, 4 => true | 4, 3 => true  -- d-e
  | 4, 5 => true | 5, 4 => true  -- e-f
  | _, _ => false

-- N(a) = { /- 여기를 채우세요 -/ }
-- N(b) = { /- 여기를 채우세요 -/ }
-- deg(a) = /- ? -/, deg(b) = /- ? -/, deg(c) = /- ? -/
-- deg(d) = /- ? -/, deg(e) = /- ? -/, deg(f) = /- ? -/
-- 고립 꼭지점: /- ? -/, 늘어진 꼭지점: /- ? -/
```

<details>
<summary>💡 답 보기</summary>

```
N(a) = {b, e}           → deg(a) = 2
N(b) = {a, c, e, f}     → deg(b) = 4
N(c) = {b, d, f}        → deg(c) = 3
N(d) = {c, e}           → deg(d) = 2
N(e) = {a, b, d, f}     → deg(e) = 4
N(f) = {b, c, e}        → deg(f) = 3
고립 꼭지점: 없음 (모든 차수 ≥ 2)
늘어진 꼭지점: 없음 (차수 1인 꼭지점 없음)
```

**악수 정리 검증**: Σ deg = 2+4+3+2+4+3 = 18, 모서리 수 = 9, 2×9 = 18 ✓
</details>

### 연습 7.2: 악수 정리 적용 (Rosen 연습문제 3)

각각의 차수가 6인 10개의 꼭지점을 갖는 그래프에는 몇 개의 모서리가 존재하는가?

```lean
-- 악수 정리: 2m = Σ deg(v)
-- 2m = /- ? -/ × /- ? -/ = /- ? -/
-- m = /- ? -/
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 2m = 6 × 10 = 60
-- m = 30
example : 6 * 10 / 2 = 30 := by norm_num
```
</details>

### 연습 7.3: 15개 꼭지점 그래프 (Rosen 연습문제 5)

15개의 꼭지점을 가진 그래프에서 각 꼭지점의 차수가 5인 단순 그래프가 존재할 수 있는가?

```lean
-- 악수 정리: 2m = 15 × 5 = 75
-- m = 75 / 2 = /- ? -/
-- 결론: /- 존재할 수 있는가? 그 이유는? -/
```

<details>
<summary>💡 답 보기</summary>

```
2m = 15 × 5 = 75
m = 75 / 2 = 37.5

모서리의 수는 자연수여야 하므로 37.5는 불가능하다.
따라서 이런 단순 그래프는 존재할 수 없다!

다른 관점: 홀수 차수(5) 꼭지점이 15개 = 홀수 개이므로
정리 2에 의해 불가능하다.
```
</details>

### 연습 7.4: 악수 정리로 모서리 수 구하기 (Rosen 연습문제 6)

파티에서 사람들의 집합에 대해 한 사람이 다른 사람과 악수하는 사람의 합(손의 합)이 짝수임을 보여라. 누구도 자신의 손과 악수할 수 없다고 가정한다.

```lean
-- 이것은 악수 정리의 직접적 응용이다!
-- 파티 = 그래프, 사람 = 꼭지점, 악수 = 모서리
-- 악수 정리: Σ deg(v) = 2m (항상 짝수!)
theorem handshake_sum_even (adj : Fin n → Fin n → Bool)
  (h_sym : ∀ i j, adj i j = adj j i)
  (h_no_self : ∀ i, adj i i = false) :
  Even (sumDegrees adj) := by
  sorry  -- 2m은 항상 짝수
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 핵심: sumDegrees = 2 * countEdges이므로 항상 짝수
-- 구체적으로:
-- sumDegrees adj
--   = Σ v, |{u | adj v u}|
--   = Σ v, Σ u, (if adj v u then 1 else 0)
--   = Σ (v,u), (if adj v u then 1 else 0)    -- 합의 교환
-- adj가 대칭이므로 adj v u = adj u v
-- 각 쌍 {v,u}이 합에 2번 기여 → 합은 항상 짝수!

-- 간단한 증명: ⟨countEdges adj, rfl⟩처럼
-- Even (2 * m)은 자명
```
</details>

### 연습 7.5: 완전 그래프의 차수와 모서리 수

다음 표를 완성하라:

```
| 그래프 | 꼭지점 수 | 각 꼭지점의 차수 | 모서리 수 |
|--------|---------|-------------|---------|
| K₃     | 3       | /- ? -/     | /- ? -/ |
| K₅     | 5       | /- ? -/     | /- ? -/ |
| K₈     | 8       | /- ? -/     | /- ? -/ |
| Kₙ     | n       | /- ? -/     | /- ? -/ |
```

<details>
<summary>💡 답 보기</summary>

```
| 그래프 | 꼭지점 수 | 각 꼭지점의 차수 | 모서리 수      |
|--------|---------|-------------|-------------|
| K₃     | 3       | 2           | 3           |
| K₅     | 5       | 4           | 10          |
| K₈     | 8       | 7           | 28          |
| Kₙ     | n       | n-1         | n(n-1)/2    |
```

**모서리 수 공식**: Kₙ의 모서리 수 = C(n,2) = n(n-1)/2

**악수 정리 검증** (K₈): Σ deg = 8 × 7 = 56 = 2 × 28 ✓
</details>

### 연습 7.6: 사이클과 휠의 차수

```
| 그래프 | 꼭지점 수 | 차수 수열                | 모서리 수 |
|--------|---------|----------------------|---------|
| C₅     | 5       | /- ? -/              | /- ? -/ |
| W₅     | 6       | /- ? -/              | /- ? -/ |
| Q₃     | 8       | /- ? -/              | /- ? -/ |
```

<details>
<summary>💡 답 보기</summary>

```
| 그래프 | 꼭지점 수 | 차수 수열                | 모서리 수 |
|--------|---------|----------------------|---------|
| C₅     | 5       | [2, 2, 2, 2, 2]      | 5       |
| W₅     | 6       | [5, 3, 3, 3, 3, 3]   | 10      |
| Q₃     | 8       | [3,3,3,3,3,3,3,3]    | 12      |
```

**C₅**: 모든 차수 2, 모서리 5개 → 2×5 = 10 = Σdeg ✓
**W₅**: 중심 차수 5, 테두리 차수 3×5 = 15, 합 = 20 = 2×10 ✓
**Q₃**: 모든 차수 3, 8×3 = 24 = 2×12 ✓
</details>

---

## 8. 연습 문제 — 레벨 2: Skeleton 채우기

### 연습 8.1: 대칭 인접 행렬의 차수 합 (악수 정리 구현)

```lean
-- 악수 정리: 차수의 합은 항상 짝수임을 보이자
-- (모서리 수의 2배이므로)
theorem sum_degrees_even
  (adj : Fin n → Fin n → Bool)
  (h_sym : ∀ i j : Fin n, adj i j = adj j i)
  (h_irr : ∀ i : Fin n, adj i i = false) :
  Even (Finset.univ.sum fun v => (Finset.univ.filter fun u => adj v u == true).card) := by
  -- 힌트: 이중 합 Σ_v Σ_u [adj v u]를 생각하자
  -- adj가 대칭이므로 Σ_v Σ_u [adj v u] = Σ_u Σ_v [adj u v]
  -- 따라서 합은 자기 자신과 같고, 2로 나누어 떨어진다
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 핵심 아이디어:
-- S := Σ v, Σ u, (if adj v u then 1 else 0)
-- S는 각 모서리 {v, u}를 (v, u)와 (u, v) 두 번 세므로
-- S = 2 * (모서리 수)
-- 따라서 S는 짝수이다.

-- 형식적 증명은 Finset.sum_comm을 사용하여
-- Σ v u, f(v,u) = Σ u v, f(v,u) = Σ u v, f(u,v) (대칭에 의해)
-- 를 보인 후, 합이 2의 배수임을 도출한다.
```
</details>

### 연습 8.2: 완전 그래프의 차수 증명

```lean
-- Kₙ에서 모든 꼭지점의 차수가 n-1임을 증명하라
theorem complete_graph_degree (n : ℕ) (hn : n ≥ 2) (v : Fin n) :
  degree (completeGraph n) v = n - 1 := by
  -- degree = |{u | u ≠ v}| = n - 1
  unfold degree neighbors
  -- 힌트: Finset.univ.filter (fun u => u != v)의 크기는 n - 1
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 핵심: {u : Fin n | u ≠ v}의 크기는 n - 1
-- Finset.card_univ_diff_singleton과 유사한 보조 정리를 사용
-- 또는 직접:
-- card (univ.filter (· ≠ v)) = card univ - card {v} = n - 1
```
</details>

### 연습 8.3: 방향성 그래프 차수 합 (정리 3)

```lean
-- 방향성 그래프에서 입력차수의 합 = 출력차수의 합 = 모서리 수
theorem digraph_degree_sum (edge : Fin n → Fin n → Bool) :
  (Finset.univ.sum fun v => (Finset.univ.filter fun u => edge u v == true).card)
  = (Finset.univ.sum fun v => (Finset.univ.filter fun u => edge v u == true).card) := by
  -- 힌트: Finset.sum_comm을 사용하여 합의 순서를 교환
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- Σ_v |{u | edge u v}| = Σ_v Σ_u [edge u v]
--                       = Σ_u Σ_v [edge u v]  (sum_comm)
--                       = Σ_u |{v | edge u v}|
-- 이것이 바로 Σ_v deg⁻(v) = Σ_u deg⁺(u) = |E|
```
</details>

---

## 9. 연습 문제 — 레벨 3: sorry 채우기 (독립 증명)

### 연습 9.1: 정규 그래프의 모서리 수

```lean
-- k-정규 그래프에서 모서리 수 = n*k/2를 증명하라
-- (정확히는 2 * 모서리 수 = n * k)
theorem regular_graph_edges (n k : ℕ)
  (adj : Fin n → Fin n → Bool)
  (h_sym : ∀ i j, adj i j = adj j i)
  (h_irr : ∀ i, adj i i = false)
  (h_reg : ∀ v : Fin n, degree adj v = k) :
  2 * countEdges adj = n * k := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 증명 전략:
-- 1. 악수 정리: 2 * countEdges = Σ deg(v)
-- 2. k-정규: Σ deg(v) = Σ k = n * k
-- 따라서 2 * countEdges = n * k
```
</details>

### 연습 9.2: 완전 그래프의 모서리 수 공식

```lean
-- K_n의 모서리 수가 n*(n-1)/2임을 증명하라
theorem complete_edge_count (n : ℕ) (hn : n ≥ 1) :
  countEdges (completeGraph n) = n * (n - 1) / 2 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 전략:
-- 1. Kₙ은 (n-1)-정규
-- 2. 정규 그래프 정리: 2m = n × (n-1)
-- 3. m = n × (n-1) / 2
-- 또는 직접: countEdges = |{(i,j) | i < j}| = C(n, 2)
```
</details>

### 연습 9.3: Cₙ의 모서리 수

```lean
-- 사이클 Cₙ (n ≥ 3)의 모서리 수가 n임을 증명하라
theorem cycle_edge_count (n : ℕ) (hn : n ≥ 3) :
  -- Cₙ은 2-정규이므로 2m = n × 2 → m = n
  2 * n = n * 2 := by
  sorry -- ring으로 해결 가능!
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem cycle_edge_count (n : ℕ) (hn : n ≥ 3) :
  2 * n = n * 2 := by ring
```
</details>

### 연습 9.4: 홀수 차수 꼭지점 수의 짝수성

```lean
-- 구체적 그래프에서 홀수 차수 꼭지점의 수가 짝수임을 검증하라
-- 그래프: K₄ (4개 꼭지점, 모든 차수 3 = 홀수)
-- 홀수 차수 꼭지점 수 = 4 (짝수) ✓

-- K₅ (5개 꼭지점, 모든 차수 4 = 짝수)
-- 홀수 차수 꼭지점 수 = 0 (짝수) ✓

example : Even 4 := ⟨2, by ring⟩
example : Even 0 := ⟨0, by ring⟩
```

---

## 10. 핵심 요약

이 파트에서 배운 것을 정리하면:

1. **인접**(adjacent): 모서리로 직접 연결된 두 꼭지점. Lean에서는 `Adj u v : Prop`으로 표현한다.
2. **이웃 집합** N(v): v와 인접한 모든 꼭지점의 집합. Lean에서는 `Finset.filter`로 계산한다.
3. **차수**(degree): 꼭지점에 붙은 모서리 수. 단순 그래프에서 deg(v) = |N(v)|이다.
4. **고립 꼭지점**: deg = 0, **늘어진 꼭지점**: deg = 1.
5. **악수 정리**: 2m = Σ deg(v). 차수의 합은 항상 짝수!
6. **홀수 차수 정리**: 홀수 차수 꼭지점의 수는 짝수.
7. **방향성 그래프**: 입력차수 deg⁻(v)와 출력차수 deg⁺(v). Σ deg⁻ = Σ deg⁺ = |E|.
8. **완전 그래프** Kₙ: 모든 쌍이 인접, (n-1)-정규, 모서리 = n(n-1)/2.
9. **사이클** Cₙ: 원형 연결, 2-정규, 모서리 = n.
10. **휠** Wₙ: Cₙ + 중심, 중심 차수 = n, 모서리 = 2n.
11. **n-큐브** Qₙ: 비트 스트링, n-정규, 꼭지점 = 2ⁿ, 모서리 = n·2^(n-1).
12. **정규 그래프**: 모든 차수 동일. k-정규이면 모서리 = nk/2.
13. **차수 수열**: 차수를 내림차순 정렬한 것.

---

> **다음 파트 예고**: Part 13-D에서는 **이분 그래프**(bipartite graph), **매칭**(matching), **홀의 결혼이론**(Hall's marriage theorem)을 다루고, 그래프의 **부분그래프**, **합집합**, **모서리 축약** 등 그래프 조작을 배운다!
