# Lean4 완전 정복 가이드 —  Part 13-E: 그래프 표현방법과 동형 그래프 (1) — 인접리스트, 인접행렬, 결합행렬

> **Rosen 이산수학 8판 · Section 10.3 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 13-C, 13-D에서는 그래프의 **기본 용어**(인접, 차수, 악수 정리)와 **특수한 그래프**(완전 그래프, 이분 그래프 등)를 배웠다. 이번 Part 13-E에서는 그래프를 컴퓨터에서 **어떻게 저장하고 표현하는지**, 그리고 두 그래프가 **같은 구조**인지(동형인지) 판별하는 방법을 배운다.

이 파트에서 다루는 내용:

1. **인접 리스트**(adjacency list) — 각 꼭지점마다 이웃을 나열
2. **인접 행렬**(adjacency matrix) — 0과 1로 된 정사각 행렬
3. **결합 행렬**(incidence matrix) — 꼭지점×모서리 행렬
4. **인접 리스트 vs 인접 행렬**의 장단점
5. **동형 그래프**(isomorphic graphs)의 정의
6. **그래프 불변성**(graph invariant) — 동형 판별 도구
7. Lean 4에서 행렬과 그래프 동형을 표현하고 증명하기

> **핵심 비유**: 그래프를 표현하는 것은 마치 친구 관계를 기록하는 것과 같다. **인접 리스트**는 "철수의 친구: 영희, 민수"처럼 각 사람마다 친구 목록을 적는 것이고, **인접 행렬**은 모든 사람 쌍에 대해 "친구인가? 예/아니오"를 표에 적는 것이다. 두 방법 모두 같은 정보를 담지만, 상황에 따라 편리한 방법이 다르다!

---

## 1. 그래프 표현 방법들 (Section 10.3.1~10.3.2)

### 1.1 왜 그래프를 표현해야 하는가?

그래프를 그림으로 그리면 직관적이지만, 컴퓨터는 그림을 직접 이해하지 못한다. 컴퓨터가 그래프를 다루려면 **데이터 구조**(data structure)로 표현해야 한다. 대표적으로 세 가지 방법이 있다:

1. **인접 리스트**(adjacency list): 각 꼭지점마다 인접한 꼭지점들의 목록을 저장
2. **인접 행렬**(adjacency matrix): n×n 행렬로 인접 관계를 0/1로 표현
3. **결합 행렬**(incidence matrix): n×m 행렬로 꼭지점과 모서리의 관계를 표현

> **일상적 비유**: 학교에서 학생들의 친구 관계를 기록한다고 생각하자.
> - **인접 리스트 방식**: 각 학생의 프로필에 "친구 목록"을 적는다 → 친구가 적은 학생이 많으면 효율적
> - **인접 행렬 방식**: 학생 전체를 행과 열에 놓고, 친구이면 ✓, 아니면 ✗를 적는다 → 친구가 많으면 효율적
> - **결합 행렬 방식**: 행에 학생, 열에 "관계"를 놓고, 그 관계에 포함되면 1을 적는다

### 1.2 인접 리스트 (Adjacency List)

**인접 리스트**(adjacency list)는 그래프의 각 꼭지점에 대해, 그 꼭지점과 **인접한**(adjacent) 모든 꼭지점들을 나열하는 방법이다.

#### 예제 1: 단순 그래프의 인접 리스트 (Rosen 예제 1)

다음 단순 그래프를 생각하자. 꼭지점은 {a, b, c, d, e}이고, 모서리는 {a,b}, {a,c}, {a,e}, {b,a}, {c,a}, {c,d}, {c,e}, {d,c}, {d,e}, {e,a}, {e,c}, {e,d}이다.

| **꼭지점**(vertex) | **인접 꼭지점들**(adjacent vertices) |
|:---:|:---:|
| a | b, c, e |
| b | a |
| c | a, d, e |
| d | c, e |
| e | a, c, d |

> **읽는 법**: 꼭지점 a에서 출발하면 b, c, e로 직접 갈 수 있다. 꼭지점 b에서는 a로만 갈 수 있다.

Lean 4에서 인접 리스트를 표현하는 가장 자연스러운 방법은 **함수**를 사용하는 것이다:

```lean
-- 인접 리스트: 각 꼭지점에 대해 이웃들의 리스트를 반환하는 함수
-- V는 꼭지점 타입

-- 방법 1: 함수로 표현 (가장 기본적)
inductive V5 | a | b | c | d | e
  deriving DecidableEq, Repr

open V5

-- 인접 리스트를 함수로 정의
def adjList : V5 → List V5
  | V5.a => [V5.b, V5.c, V5.e]
  | V5.b => [V5.a]
  | V5.c => [V5.a, V5.d, V5.e]
  | V5.d => [V5.c, V5.e]
  | V5.e => [V5.a, V5.c, V5.d]

-- 인접 리스트에서 인접성 판단:
-- "v의 인접 리스트에 u가 포함되어 있는가?"
def isAdjacentViaList (u v : V5) : Bool :=
  (adjList u).contains v

-- 예: a와 b가 인접하는가?
#eval isAdjacentViaList V5.a V5.b  -- true
#eval isAdjacentViaList V5.a V5.d  -- false (a와 d는 인접하지 않음!)
```

> **핵심 포인트**: 인접 리스트는 `V → List V` 타입의 함수이다. 각 꼭지점을 입력하면 이웃들의 목록을 반환한다.

#### 예제 2: 방향성 그래프의 인접 리스트 (Rosen 예제 2)

**방향성 그래프**(directed graph)에서는 화살표의 방향이 있으므로, 각 꼭지점에서 **나가는**(outgoing) 모서리의 끝점을 나열한다.

| **시작 꼭지점**(initial vertex) | **종료 꼭지점들**(terminal vertices) |
|:---:|:---:|
| a | b, c, d, e |
| b | b, d |
| c | a, c, e |
| d | (없음) |
| e | b, c, d |

```lean
-- 방향성 그래프의 인접 리스트
-- 각 꼭지점에서 "나가는" 모서리의 끝점들

def dirAdjList : V5 → List V5
  | V5.a => [V5.b, V5.c, V5.d, V5.e]  -- a에서 b,c,d,e로 화살표
  | V5.b => [V5.b, V5.d]              -- b에서 자기자신, d로 화살표
  | V5.c => [V5.a, V5.c, V5.e]        -- c에서 a, 자기자신, e로 화살표
  | V5.d => []                         -- d에서 나가는 화살표 없음!
  | V5.e => [V5.b, V5.c, V5.d]        -- e에서 b,c,d로 화살표

-- 주의: 방향성 그래프에서는 a→b이지만 b→a는 아닐 수 있다!
-- dirAdjList a에 b가 있지만, dirAdjList b에 a는 없다.
```

> **비방향 vs 방향**: 비방향 그래프에서는 인접 리스트가 대칭적이다 (a의 목록에 b가 있으면 b의 목록에도 a가 있다). 방향성 그래프에서는 그렇지 않을 수 있다.

---

## 2. 인접 행렬 (Section 10.3.3)

### 2.1 인접 행렬의 정의

> **정의** (Rosen): 그래프 G = (V, E)에서 |V| = n인 단순 그래프라 하자. G의 각 꼭지점 v₁, v₂, ..., vₙ을 임의로 나열했다고 가정한다. G의 **인접 행렬**(adjacency matrix) **A** (또는 **A**_G)는 n차의 0-1 행렬이다. 이 행렬의 (i, j)항은 G의 꼭지점을 이용하여 다음과 같이 정의된다:
>
> - a_ij = 1 : v_i와 v_j가 인접할 때
> - a_ij = 0 : v_i와 v_j가 인접하지 않을 때

쉽게 말해서, **인접 행렬**은 "이 두 꼭지점이 연결되어 있는가?"라는 질문에 대한 답을 표로 정리한 것이다.

### 2.2 인접 행렬의 핵심 성질

인접 행렬에는 중요한 성질들이 있다:

1. **대각선은 0**: 단순 그래프에는 **루프**(loop)가 없으므로, a_ii = 0이다 (i = 1, 2, ..., n).
2. **대칭 행렬**: 단순 그래프의 인접 행렬은 **대칭적**(symmetric)이다. 즉, a_ij = a_ji이다. 왜냐하면 v_i와 v_j가 인접하면 v_j와 v_i도 인접하기 때문이다 (비방향이니까!).
3. **유사 그래프**: 유사 그래프(pseudograph)에서는 루프가 있을 수 있으므로 대각선이 0이 아닐 수 있고, 다중 모서리가 있으면 항이 1보다 클 수 있다.

### 2.3 예제 3: 단순 그래프 → 인접 행렬 (Rosen 예제 3)

꼭지점 {a, b, c, d}에 대해, 모서리가 {a,b}, {a,c}, {a,d}, {b,c}인 단순 그래프를 생각하자.

꼭지점 a, b, c, d에 대응하여 4개의 행과 열을 나열하면 인접 행렬은:

```
     a  b  c  d
a [  0  1  1  1 ]
b [  1  0  1  0 ]
c [  1  1  0  0 ]
d [  1  0  0  0 ]
```

> **읽는 법**: (a, b) 위치가 1이면 a와 b가 연결되어 있다. (b, d) 위치가 0이면 b와 d는 연결되어 있지 않다.

```lean
-- Lean 4에서 인접 행렬 표현
-- 방법 1: Fin n → Fin n → ℕ 함수로 표현 (Part 12-D에서 배운 방법)

-- 4개 꼭지점 {0=a, 1=b, 2=c, 3=d}
-- 모서리: {a,b}, {a,c}, {a,d}, {b,c}

def adjMatrix_ex3 : Fin 4 → Fin 4 → ℕ := fun i j =>
  match i.val, j.val with
  | 0, 1 => 1 | 1, 0 => 1   -- {a,b}
  | 0, 2 => 1 | 2, 0 => 1   -- {a,c}
  | 0, 3 => 1 | 3, 0 => 1   -- {a,d}
  | 1, 2 => 1 | 2, 1 => 1   -- {b,c}
  | _, _ => 0

-- 방법 2: Mathlib의 Matrix 표기법 사용
-- !![0, 1, 1, 1; 1, 0, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0]

-- 인접 행렬이 대칭적임을 확인
-- 즉, adjMatrix_ex3 i j = adjMatrix_ex3 j i
theorem adjMatrix_ex3_symm (i j : Fin 4) :
    adjMatrix_ex3 i j = adjMatrix_ex3 j i := by
  fin_cases i <;> fin_cases j <;> simp [adjMatrix_ex3]
```

### 2.4 예제 4: 인접 행렬 → 그래프 그리기 (Rosen 예제 4)

인접 행렬이 주어지면, 역으로 그래프를 그릴 수 있다:

```
     a  b  c  d
a [  0  1  1  0 ]
b [  1  0  0  1 ]
c [  1  0  0  1 ]
d [  0  1  1  0 ]
```

이 행렬에서 1인 위치를 읽으면: 모서리 = {a,b}, {a,c}, {b,d}, {c,d}. 이것은 **사각형** 모양의 그래프이다!

```lean
-- 인접 행렬에서 SimpleGraph 만들기
-- 핵심: 행렬의 (i,j)가 1이면 Adj i j = True

def matrixToGraph (M : Fin n → Fin n → ℕ)
    (h_symm : ∀ i j, M i j = M j i)
    (h_loop : ∀ i, M i i = 0) : SimpleGraph (Fin n) where
  Adj i j := M i j ≠ 0
  symm := by
    intro i j h
    rw [h_symm] at h
    exact h
  loopless := by
    intro i h
    exact h (h_loop i)
```

### 2.5 유사 그래프의 인접 행렬 (Rosen 예제 5)

**유사 그래프**(pseudograph)에서는 다중 모서리와 루프가 허용되므로, 인접 행렬의 항이 1보다 클 수 있다.

예: 꼭지점 {a, b, c, d}에 대해 a와 b 사이에 모서리가 3개, c와 d 사이에 모서리가 2개인 유사 그래프:

```
     a  b  c  d
a [  0  3  0  2 ]
b [  3  0  1  1 ]
c [  0  1  1  2 ]
d [  2  1  2  0 ]
```

> **대각선의 의미**: c와 c 사이에 루프가 1개 있으면 (c, c) 위치에 1이 온다. 유사 그래프에서는 대각선이 0이 아닐 수 있다!

### 2.6 방향성 그래프의 인접 행렬

방향성 그래프 G = (V, E)의 인접 행렬은 비대칭일 수 있다:

- a_ij = 1 : v_i에서 v_j로 가는 모서리가 존재할 때
- a_ij = 0 : 그렇지 않을 때

> **핵심 차이**: v_i에서 v_j로 가는 모서리가 있어도, v_j에서 v_i로 가는 모서리는 없을 수 있다. 따라서 a_ij ≠ a_ji일 수 있고, 인접 행렬은 **비대칭**(asymmetric)이다!

```lean
-- 방향성 그래프의 인접 행렬
-- 비대칭일 수 있으므로 symm 조건이 없다!

structure SimpleDigraph (V : Type) where
  Adj : V → V → Prop
  loopless : ∀ v, ¬ Adj v v  -- 루프 없음만 요구 (대칭은 요구하지 않음!)

-- 방향성 그래프의 인접 행렬
def dirAdjMatrix (G : SimpleDigraph (Fin n)) : Fin n → Fin n → ℕ :=
  fun i j => if G.Adj i j then 1 else 0
```

---

## 3. 인접 리스트와 인접 행렬의 장단점

그래프를 표현할 때 인접 리스트와 인접 행렬 중 어떤 것을 사용할지는 그래프의 **밀도**(density)에 따라 결정된다.

### 3.1 비교표

| 기준 | **인접 리스트**(adjacency list) | **인접 행렬**(adjacency matrix) |
|:---|:---|:---|
| 저장 공간 | O(n + m) (n=꼭지점, m=모서리) | O(n²) |
| 모서리 존재 확인 | O(c) — 목록 탐색 필요 (c는 차수) | O(1) — 즉시 확인! |
| **희박한**(sparse) 그래프 | ✅ 효율적 | ❌ 비효율적 (0이 대부분) |
| **촘촘한**(dense) 그래프 | ❌ 비효율적 | ✅ 효율적 |
| 적합한 상황 | 모서리가 적은 그래프 | 모서리가 많은 그래프 |

> **희박하다**(sparse): 모서리의 수가 꼭지점 수에 비해 적은 그래프. 예: 도로 네트워크 (각 교차로에서 나가는 도로는 보통 3~4개).
>
> **촘촘하다**(dense): 모서리의 수가 가능한 최대 모서리 수에 가까운 그래프. 예: 완전 그래프 K_n (모든 쌍이 연결됨).

### 3.2 Lean 4에서의 비교

```lean
-- 희박한 그래프: 인접 리스트가 유리
-- 100개 꼭지점에 모서리가 150개인 그래프

-- 인접 리스트: 약 300개의 항목 저장 (각 모서리가 양쪽에 한 번씩)
-- 인접 행렬: 10000개의 항목 저장 (대부분 0!)

-- 인접 리스트로 인접성 확인: 평균 3개 탐색
-- 인접 행렬로 인접성 확인: 즉시 (인덱스 접근)

-- Lean 4에서 인접 리스트 기반 그래프
structure AdjListGraph (V : Type) [DecidableEq V] where
  vertices : List V
  neighbors : V → List V
  -- 대칭 조건: u의 이웃에 v가 있으면 v의 이웃에도 u가 있어야 함
  symm_cond : ∀ u v, v ∈ neighbors u → u ∈ neighbors v

-- Lean 4에서 인접 행렬 기반 그래프
structure AdjMatrixGraph (n : ℕ) where
  matrix : Fin n → Fin n → ℕ
  symm_cond : ∀ i j, matrix i j = matrix j i
  loop_free : ∀ i, matrix i i = 0
```

---

## 4. 결합 행렬 (Section 10.3.4)

### 4.1 결합 행렬의 정의

> **정의** (Rosen): 그래프를 표현하는 또 다른 일반적인 방법은 **결합 행렬**(incidence matrix)을 사용하는 것이다. G = (V, E)라는 비방향성 그래프가 아래 순서대로의 n개의 꼭지점 v₁, v₂, ..., vₙ과 m개의 모서리 e₁, e₂, ..., eₘ을 갖는다 하자. V와 E에 대한 결합 행렬은 n × m 행렬 **M** = [m_ij]이고 성분은 아래와 같이 정의된다:
>
> - m_ij = 1 : 모서리 e_j가 v_i와 연결된 경우
> - m_ij = 0 : 그렇지 않을 경우

쉽게 말해서, 결합 행렬은 "이 꼭지점이 이 모서리에 **참여**(참가, 붙어 있다)하고 있는가?"를 기록한 표이다.

### 4.2 예제 6: 비방향 그래프의 결합 행렬 (Rosen 예제 6)

5개 꼭지점 {v₁, v₂, v₃, v₄, v₅}과 6개 모서리 {e₁, e₂, e₃, e₄, e₅, e₆}을 가진 그래프:

모서리 연결 관계:
- e₁: {v₁, v₄} — v₁과 v₄를 연결
- e₂: {v₁, v₅} — v₁과 v₅를 연결
- e₃: {v₂, v₄} — v₂와 v₄를 연결
- e₄: {v₂, v₅} — v₂와 v₅를 연결
- e₅: {v₃, v₅} — v₃과 v₅를 연결
- e₆: {v₃, v₂} — v₃과 v₂를 연결

결합 행렬 (5×6):

```
       e₁  e₂  e₃  e₄  e₅  e₆
v₁ [   1   1   0   0   0   0  ]
v₂ [   0   0   1   1   0   1  ]
v₃ [   0   0   0   0   1   1  ]
v₄ [   1   0   1   0   0   0  ]
v₅ [   0   1   0   1   1   0  ]
```

> **읽는 법**: v₁ 행을 보면, e₁과 e₂에 1이 있다. 이것은 v₁이 모서리 e₁과 e₂에 참여(연결)한다는 뜻이다. 각 열(모서리)에는 정확히 2개의 1이 있다 — 각 모서리는 정확히 2개의 끝점을 갖기 때문이다!

```lean
-- 결합 행렬: Fin n → Fin m → ℕ (n = 꼭지점 수, m = 모서리 수)

-- 예제 6의 결합 행렬
def incMatrix_ex6 : Fin 5 → Fin 6 → ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 0, 1 => 1  -- v₁: e₁, e₂에 참여
  | 1, 2 => 1 | 1, 3 => 1 | 1, 5 => 1  -- v₂: e₃, e₄, e₆에 참여
  | 2, 4 => 1 | 2, 5 => 1  -- v₃: e₅, e₆에 참여
  | 3, 0 => 1 | 3, 2 => 1  -- v₄: e₁, e₃에 참여
  | 4, 1 => 1 | 4, 3 => 1 | 4, 4 => 1  -- v₅: e₂, e₄, e₅에 참여
  | _, _ => 0

-- 결합 행렬의 핵심 성질:
-- 각 열(모서리)의 합 = 2 (모서리는 정확히 2개의 끝점을 가짐)
-- 각 행(꼭지점)의 합 = 그 꼭지점의 차수!

-- 행의 합 = 차수
def rowSum (M : Fin n → Fin m → ℕ) (i : Fin n) : ℕ :=
  Finset.sum Finset.univ (fun j => M i j)

-- 열의 합 = 2 (단순 그래프에서)
def colSum (M : Fin n → Fin m → ℕ) (j : Fin m) : ℕ :=
  Finset.sum Finset.univ (fun i => M i j)
```

### 4.3 결합 행렬의 핵심 성질

| 성질 | 설명 |
|:---|:---|
| 각 열의 합 = 2 | 각 모서리는 정확히 2개의 끝점을 가진다 |
| 각 행의 합 = deg(v) | 그 꼭지점의 차수와 같다 |
| 루프 | 루프는 해당 열의 한 꼭지점 행에 정확히 1개의 1을 준다 |
| 다중 모서리 | 같은 두 꼭지점에 대해 동일한 패턴의 열이 여러 개 나온다 |

---

## 5. 동형 그래프 (Section 10.3.5)

### 5.1 동형의 직관

때때로 같은 방법으로 두 개의 다른 그래프를 그리는 것이 가능한지 알 필요가 있다. 즉, 꼭지점에 주어지는 이름을 고려하지 않을 때 두 개의 그래프는 같은 구조를 갖는가?

> **일상적 비유**: 두 학교의 친구 관계 그래프를 비교한다고 하자. 학생들의 이름은 다르지만, "A학교에서 친구인 쌍의 패턴"과 "B학교에서 친구인 쌍의 패턴"이 완전히 같다면, 두 그래프는 **동형**(isomorphic)이다.
>
> 더 쉽게: 그래프를 고무줄로 만들어서 꼭지점의 이름을 지우면, 모양이 완전히 같아지는 것이다!

### 5.2 동형의 정의

> **정의 1** (Rosen): 단순 그래프 G₁ = (V₁, E₁)과 G₂ = (V₂, E₂) 사이에 V₁의 모든 a, b에 대해 a, b가 G₁에서 인접하면 f(a)와 f(b)도 G₂에서 인접하고 그 역도 성립하는, V₁에서 V₂로의 **전단사 함수**(bijection) f가 존재하면, 두 그래프는 **동형**(isomorphic)이라고 한다. 이때 함수 f를 **동형사상**(isomorphism)이라 부른다.

이것을 조건별로 분해해보자:

1. **전단사 함수**: f는 일대일(단사) + 위로(전사) 함수이다. 즉, G₁의 모든 꼭지점이 G₂의 정확히 하나의 꼭지점과 대응된다.
2. **인접 보존**: G₁에서 인접한 쌍은 f를 적용해도 G₂에서 인접하다.
3. **역도 성립**: G₂에서 f(a)와 f(b)가 인접하면, G₁에서도 a와 b가 인접하다 (즉, 인접하지 않은 쌍도 보존됨).

```lean
-- Lean 4에서 그래프 동형의 정의
-- G₁과 G₂가 같은 타입의 꼭지점을 가질 때의 간단한 정의

def GraphIso (G₁ G₂ : SimpleGraph V) : Prop :=
  ∃ f : V ≃ V,  -- f는 V에서 V로의 전단사 함수 (동치, Equiv)
    ∀ u v, G₁.Adj u v ↔ G₂.Adj (f u) (f v)

-- 더 일반적으로: 꼭지점 타입이 다를 때
def GraphIso' (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : Prop :=
  ∃ f : V₁ ≃ V₂,
    ∀ u v, G₁.Adj u v ↔ G₂.Adj (f u) (f v)

-- Mathlib에서는 SimpleGraph.Iso로 정의되어 있다:
-- G ≃g H 표기법 사용
```

### 5.3 예제 8: 동형인 그래프 (Rosen 예제 8)

G = (V, E)와 H = (W, F)가 동형임을 보이자.

G의 꼭지점: {u₁, u₂, u₃, u₄}  
H의 꼭지점: {v₁, v₂, v₃, v₄}

G의 인접 관계: u₁~u₂, u₁~u₃, u₂~u₄, u₃~u₄  
H의 인접 관계: v₁~v₂, v₁~v₃, v₂~v₄, v₃~v₄

동형사상 f: f(u₁) = v₁, f(u₂) = v₄, f(u₃) = v₃, f(u₄) = v₂

이 함수가 인접성을 보존하는지 확인:
- u₁~u₂ → f(u₁)~f(u₂) = v₁~v₄ ✓ (H에서 인접)
- u₁~u₃ → f(u₁)~f(u₃) = v₁~v₃ ✓
- u₂~u₄ → f(u₂)~f(u₄) = v₄~v₂ ✓
- u₃~u₄ → f(u₃)~f(u₄) = v₃~v₂ ✓

```lean
-- 예제 8: 두 그래프의 동형 증명

-- 그래프 G (4개 꼭지점)
def G_ex8 : SimpleGraph (Fin 4) where
  Adj := fun i j => match i.val, j.val with
    | 0, 1 => True | 1, 0 => True  -- u₁~u₂
    | 0, 2 => True | 2, 0 => True  -- u₁~u₃
    | 1, 3 => True | 3, 1 => True  -- u₂~u₄
    | 2, 3 => True | 3, 2 => True  -- u₃~u₄
    | _, _ => False
  symm := by intros i j h; revert h; fin_cases i <;> fin_cases j <;> simp_all
  loopless := by intro i; fin_cases i <;> simp_all

-- 그래프 H (4개 꼭지점, 다른 인접 패턴)
def H_ex8 : SimpleGraph (Fin 4) where
  Adj := fun i j => match i.val, j.val with
    | 0, 1 => True | 1, 0 => True  -- v₁~v₂
    | 0, 2 => True | 2, 0 => True  -- v₁~v₃
    | 1, 3 => True | 3, 1 => True  -- v₂~v₄
    | 2, 3 => True | 3, 2 => True  -- v₃~v₄
    | _, _ => False
  symm := by intros i j h; revert h; fin_cases i <;> fin_cases j <;> simp_all
  loopless := by intro i; fin_cases i <;> simp_all

-- 이 경우 두 그래프는 사실 동일한 인접 행렬을 가진다!
-- 동형사상은 항등 함수로 충분하다.
-- 더 흥미로운 경우: 꼭지점 번호 매핑이 다른 경우
```

### 5.4 동형이 아닌 그래프 판별 — 불변성 (Rosen 예제 9~10)

두 그래프가 동형이 **아님**을 보이려면, 동형이면 반드시 같아야 하는 특성(**그래프 불변성**, graph invariant)이 다름을 보이면 된다.

#### 그래프 불변성의 종류

동형인 두 그래프는 다음이 **반드시** 같다:

| **불변성**(invariant) | 설명 |
|:---|:---|
| 꼭지점의 수 | \|V₁\| = \|V₂\| |
| 모서리의 수 | \|E₁\| = \|E₂\| |
| **차수 수열**(degree sequence) | 정렬된 차수 목록이 같아야 함 |
| 특정 길이의 **단순 순환**(simple cycle) 존재 | 길이 k인 순환이 있으면 다른 쪽에도 있어야 함 |

> **주의**: 이 불변성이 모두 같다고 해서 반드시 동형인 것은 **아니다**! 불변성이 다르면 비동형이 확실하지만, 같으면 추가 확인이 필요하다.

```lean
-- 예제 9: 동형이 아닌 그래프 (Rosen 예제 9)
-- G: 5개 꼭지점, 6개 모서리
-- H: 5개 꼭지점, 6개 모서리, 차수 1인 꼭지점이 있음
-- G에는 차수 1인 꼭지점이 없음 → 비동형!

-- 차수 수열 비교로 비동형 판별
-- G의 차수 수열: [2, 3, 3, 2, 2] (정렬: [2, 2, 2, 3, 3])
-- H의 차수 수열: [1, 2, 3, 3, 3] (정렬: [1, 2, 3, 3, 3])
-- 다르므로 비동형!

-- Lean 4에서 차수 수열 계산
def degreeSeq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  (List.ofFn (fun i => Finset.card (Finset.filter (G.Adj i) Finset.univ))).mergeSort (· ≤ ·)
```

---

## 6. 동형 확인 방법: 인접 행렬 활용 (Rosen 예제 11)

### 6.1 인접 행렬을 이용한 동형 확인

그래프 G의 꼭지점 집합을 H의 꼭지점 집합으로 보내는 함수 f가 동형함수임을 보이려면, **G의 인접 행렬의 행과 열에 이름을 f로 보낸 대응하는 상의 행과 열을 비교하여** H의 인접 행렬과 같다는 것을 보여야 한다.

더 쉽게 말하면: G의 인접 행렬에서 행과 열의 순서를 f에 따라 재배열하면, H의 인접 행렬과 똑같아져야 한다.

### 6.2 예제 11: 인접 행렬로 동형 확인 (Rosen 예제 11)

G: 6개 꼭지점 {u₁, ..., u₆}  
H: 6개 꼭지점 {v₁, ..., v₆}

G의 인접 행렬 A_G:

```
       u₁  u₂  u₃  u₄  u₅  u₆
u₁ [    0   1   0   1   0   0  ]
u₂ [    1   0   1   0   0   1  ]
u₃ [    0   1   0   1   0   0  ]
u₄ [    1   0   1   0   1   0  ]
u₅ [    0   0   0   1   0   1  ]
u₆ [    0   1   0   0   1   0  ]
```

동형사상 f: f(u₁) = v₆, f(u₂) = v₃, f(u₃) = v₄, f(u₄) = v₅, f(u₅) = v₁, f(u₆) = v₂

H의 인접 행렬을 f에 대응하는 순서(v₆, v₃, v₄, v₅, v₁, v₂)로 재배열하면 A_G와 같아진다!

A_G = A_H 이므로 f는 모서리들도 보존하는 함수이다. 그러므로 f는 동형사상이고 G와 H는 동형 그래프이다.

```lean
-- 인접 행렬 재배열로 동형 확인
-- 핵심 아이디어: A_G[i][j] = A_H[f(i)][f(j)]이면 동형

-- 동형사상 확인 함수
def checkIso (A_G A_H : Fin n → Fin n → ℕ) (f : Fin n → Fin n) : Bool :=
  (Finset.univ.product Finset.univ).forall
    (fun p => A_G p.1 p.2 == A_H (f p.1) (f p.2))

-- 정리: A_G = f로 재배열한 A_H이면 동형
theorem iso_iff_matrix_eq (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : Fin n ≃ Fin n)
    (h : ∀ i j, G.Adj i j ↔ H.Adj (f i) (f j)) :
    GraphIso' G H := by
  exact ⟨f, h⟩
```

---

## 7. 연습문제

### 연습 7.1: 인접 리스트 작성 (skeleton — 괄호 채우기)

**문제**: 다음 단순 그래프의 인접 리스트를 Lean 4로 작성하라. 꼭지점 {0, 1, 2, 3}에 대해 모서리는 {0,1}, {0,2}, {1,2}, {2,3}이다.

```lean
def adjList_ex1 : Fin 4 → List (Fin 4)
  | ⟨0, _⟩ => [⟨【①】, by omega⟩, ⟨【②】, by omega⟩]   -- 0의 이웃
  | ⟨1, _⟩ => [⟨【③】, by omega⟩, ⟨【④】, by omega⟩]   -- 1의 이웃
  | ⟨2, _⟩ => [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨【⑤】, by omega⟩]  -- 2의 이웃
  | ⟨3, _⟩ => [⟨【⑥】, by omega⟩]  -- 3의 이웃
```

<details>
<summary>📝 답 보기</summary>

```lean
def adjList_ex1 : Fin 4 → List (Fin 4)
  | ⟨0, _⟩ => [⟨1, by omega⟩, ⟨2, by omega⟩]     -- ①=1, ②=2
  | ⟨1, _⟩ => [⟨0, by omega⟩, ⟨2, by omega⟩]     -- ③=0, ④=2
  | ⟨2, _⟩ => [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨3, by omega⟩]  -- ⑤=3
  | ⟨3, _⟩ => [⟨2, by omega⟩]                      -- ⑥=2
```

**설명**: 모서리 {0,1}이 있으므로 0의 이웃에 1이, 1의 이웃에 0이 포함된다 (비방향이니까!). 모서리 {2,3}이 있으므로 2의 이웃에 3이, 3의 이웃에 2가 포함된다.
</details>

---

### 연습 7.2: 인접 행렬 작성 (skeleton — 괄호 채우기)

**문제**: 꼭지점 {0, 1, 2}에 대해 모서리가 {0,1}, {1,2}인 **경로 그래프**(path graph) P₃의 인접 행렬을 완성하라.

```lean
def adjMatrix_P3 : Fin 3 → Fin 3 → ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 【①】  -- 0과 0: 루프?
  | 0, 1 => 【②】  -- 0과 1: 인접?
  | 0, 2 => 【③】  -- 0과 2: 인접?
  | 1, 0 => 【④】  -- 1과 0: 인접?
  | 1, 1 => 【⑤】  -- 1과 1: 루프?
  | 1, 2 => 【⑥】  -- 1과 2: 인접?
  | 2, 0 => 【⑦】  -- 2과 0: 인접?
  | 2, 1 => 【⑧】  -- 2과 1: 인접?
  | 2, 2 => 【⑨】  -- 2과 2: 루프?
  | _, _ => 0
```

<details>
<summary>📝 답 보기</summary>

```lean
def adjMatrix_P3 : Fin 3 → Fin 3 → ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 0  -- ①=0 (루프 없음)
  | 0, 1 => 1  -- ②=1 (0~1 인접!)
  | 0, 2 => 0  -- ③=0 (0~2 비인접)
  | 1, 0 => 1  -- ④=1 (대칭!)
  | 1, 1 => 0  -- ⑤=0 (루프 없음)
  | 1, 2 => 1  -- ⑥=1 (1~2 인접!)
  | 2, 0 => 0  -- ⑦=0 (대칭!)
  | 2, 1 => 1  -- ⑧=1 (대칭!)
  | 2, 2 => 0  -- ⑨=0 (루프 없음)
  | _, _ => 0
```

**행렬 형태**:
```
    0  1  2
0 [ 0  1  0 ]
1 [ 1  0  1 ]
2 [ 0  1  0 ]
```

**포인트**: 대각선은 모두 0 (루프 없음). 행렬이 대칭적 (단순 그래프이므로).
</details>

---

### 연습 7.3: 인접 행렬의 대칭성 증명 (skeleton)

**문제**: 다음 인접 행렬이 대칭적임을 증명하라.

```lean
-- 정의
def myAdj : Fin 3 → Fin 3 → ℕ := fun i j =>
  match i.val, j.val with
  | 0, 1 => 1 | 1, 0 => 1
  | 1, 2 => 1 | 2, 1 => 1
  | _, _ => 0

-- 증명
theorem myAdj_symm : ∀ (i j : Fin 3), myAdj i j = myAdj j i := by
  intro i j
  【빈칸】
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem myAdj_symm : ∀ (i j : Fin 3), myAdj i j = myAdj j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [myAdj]
```

**설명**: `fin_cases`는 `Fin 3`의 모든 가능한 값 (0, 1, 2)을 나열한다. `<;>`는 모든 경우에 같은 전술을 적용한다. `simp [myAdj]`는 `myAdj`의 정의를 펼쳐서 자동으로 증명한다.

이 방법이 통하는 이유: `Fin 3`은 유한 타입이므로 모든 (i, j) 쌍을 나열하면 9가지뿐이다. 각 경우를 계산으로 확인할 수 있다!
</details>

---

### 연습 7.4: 결합 행렬 작성 (skeleton)

**문제**: 3개 꼭지점 {v₀, v₁, v₂}과 2개 모서리 {e₀ = {v₀, v₁}, e₁ = {v₁, v₂}}를 가진 경로 그래프의 결합 행렬을 작성하라.

```lean
def incMatrix_path : Fin 3 → Fin 2 → ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 【①】  -- v₀은 e₀에 참여하는가?
  | 0, 1 => 【②】  -- v₀은 e₁에 참여하는가?
  | 1, 0 => 【③】  -- v₁은 e₀에 참여하는가?
  | 1, 1 => 【④】  -- v₁은 e₁에 참여하는가?
  | 2, 0 => 【⑤】  -- v₂는 e₀에 참여하는가?
  | 2, 1 => 【⑥】  -- v₂는 e₁에 참여하는가?
  | _, _ => 0
```

<details>
<summary>📝 답 보기</summary>

```lean
def incMatrix_path : Fin 3 → Fin 2 → ℕ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1  -- ①=1: v₀은 e₀={v₀,v₁}에 참여 ✓
  | 0, 1 => 0  -- ②=0: v₀은 e₁={v₁,v₂}에 참여 ✗
  | 1, 0 => 1  -- ③=1: v₁은 e₀={v₀,v₁}에 참여 ✓
  | 1, 1 => 1  -- ④=1: v₁은 e₁={v₁,v₂}에 참여 ✓
  | 2, 0 => 0  -- ⑤=0: v₂는 e₀={v₀,v₁}에 참여 ✗
  | 2, 1 => 1  -- ⑥=1: v₂는 e₁={v₁,v₂}에 참여 ✓
  | _, _ => 0
```

**행렬 형태**:
```
       e₀  e₁
v₀ [   1   0  ]
v₁ [   1   1  ]
v₂ [   0   1  ]
```

**확인**: 각 열의 합 = 2 ✓ (모서리마다 끝점 2개). v₁의 행 합 = 2 = deg(v₁) ✓ (v₁의 차수가 2).
</details>

---

### 연습 7.5: 차수 수열로 비동형 판별 (sorry)

**문제**: 다음 두 그래프가 동형이 아님을 차수 수열을 비교하여 보여라.

```lean
-- 그래프 G1: K₃ (완전 그래프 — 3개 꼭지점 모두 연결)
def G1_noiso : SimpleGraph (Fin 3) where
  Adj i j := i ≠ j
  symm := by intro i j h; exact Ne.symm h
  loopless := by intro i; exact absurd rfl

-- 그래프 G2: P₃ (경로 그래프 — 0~1~2)
def G2_noiso : SimpleGraph (Fin 3) where
  Adj := fun i j => match i.val, j.val with
    | 0, 1 => True | 1, 0 => True
    | 1, 2 => True | 2, 1 => True
    | _, _ => False
  symm := by intros i j h; revert h; fin_cases i <;> fin_cases j <;> simp_all
  loopless := by intro i; fin_cases i <;> simp_all

-- 차수 수열 비교:
-- G1의 차수 수열: [2, 2, 2] (모든 꼭지점의 차수가 2)
-- G2의 차수 수열: [1, 2, 1] (정렬: [1, 1, 2])
-- 다르므로 비동형!

theorem G1_G2_not_iso : ¬ GraphIso' G1_noiso G2_noiso := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem G1_G2_not_iso : ¬ GraphIso' G1_noiso G2_noiso := by
  intro ⟨f, hf⟩
  -- G1에서 꼭지점 0의 차수 = 2 (0~1, 0~2)
  -- G2에서 f(0)의 차수도 2여야 함
  -- G2에서 차수가 2인 꼭지점은 1뿐
  -- 따라서 f(0) = 1
  -- G1에서 꼭지점 1의 차수 = 2 (1~0, 1~2)
  -- G2에서 f(1)의 차수도 2여야 함
  -- G2에서 차수가 2인 꼭지점은 1뿐인데 이미 f(0) = 1
  -- f는 전단사이므로 f(1) ≠ f(0) = 1 — 모순!
  have h0 : G1_noiso.Adj 0 1 := by simp [G1_noiso]
  have h1 : G2_noiso.Adj (f 0) (f 1) := (hf 0 1).mp h0
  have h2 : G1_noiso.Adj 0 2 := by simp [G1_noiso]
  have h3 : G2_noiso.Adj (f 0) (f 2) := (hf 0 2).mp h2
  have h4 : G1_noiso.Adj 1 2 := by simp [G1_noiso]
  have h5 : G2_noiso.Adj (f 1) (f 2) := (hf 1 2).mp h4
  -- G2에서 각 꼭지점의 인접 꼭지점 수 확인 후 모순 도출
  fin_cases (f 0) <;> fin_cases (f 1) <;> fin_cases (f 2) <;>
    simp_all [G2_noiso, G1_noiso]
```

**핵심 전략**: G1(완전 그래프)에서는 모든 꼭지점의 차수가 2이다. G2(경로 그래프)에서는 차수 2인 꼭지점이 하나뿐(꼭지점 1)이다. 전단사 함수 f가 차수를 보존해야 하므로 3개의 꼭지점을 모두 차수 2인 곳으로 보내야 하는데, 그런 곳이 하나밖에 없으므로 모순이다!
</details>

---

### 연습 7.6: 동형인 그래프 증명 (sorry)

**문제**: 다음 두 그래프가 동형임을 보여라.

```lean
-- G: 사각형 0~1~2~3~0
def G_square : SimpleGraph (Fin 4) where
  Adj := fun i j => match i.val, j.val with
    | 0, 1 => True | 1, 0 => True
    | 1, 2 => True | 2, 1 => True
    | 2, 3 => True | 3, 2 => True
    | 3, 0 => True | 0, 3 => True
    | _, _ => False
  symm := by intros i j h; revert h; fin_cases i <;> fin_cases j <;> simp_all
  loopless := by intro i; fin_cases i <;> simp_all

-- H: 사각형 0~2~1~3~0 (다른 번호 매핑)
def H_square : SimpleGraph (Fin 4) where
  Adj := fun i j => match i.val, j.val with
    | 0, 2 => True | 2, 0 => True
    | 2, 1 => True | 1, 2 => True
    | 1, 3 => True | 3, 1 => True
    | 3, 0 => True | 0, 3 => True
    | _, _ => False
  symm := by intros i j h; revert h; fin_cases i <;> fin_cases j <;> simp_all
  loopless := by intro i; fin_cases i <;> simp_all

-- 동형사상 f: 0↦0, 1↦2, 2↦1, 3↦3
theorem square_iso : GraphIso' G_square H_square := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
-- 동형사상 정의
def f_square : Fin 4 ≃ Fin 4 where
  toFun := fun i => match i.val with
    | 0 => ⟨0, by omega⟩
    | 1 => ⟨2, by omega⟩
    | 2 => ⟨1, by omega⟩
    | 3 => ⟨3, by omega⟩
    | _ => i  -- 도달 불가
  invFun := fun i => match i.val with
    | 0 => ⟨0, by omega⟩
    | 1 => ⟨2, by omega⟩
    | 2 => ⟨1, by omega⟩
    | 3 => ⟨3, by omega⟩
    | _ => i
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem square_iso : GraphIso' G_square H_square := by
  exact ⟨f_square, by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [G_square, H_square, f_square]⟩
```

**설명**: f(0)=0, f(1)=2, f(2)=1, f(3)=3으로 매핑한다. `Equiv`를 사용하여 역함수와 양방향 역관계를 증명한다. 그 다음 `fin_cases`로 모든 (i, j) 쌍에 대해 인접성이 보존됨을 확인한다.
</details>

---

## 8. 핵심 요약

1. **인접 리스트**(adjacency list)는 각 꼭지점마다 이웃 목록을 저장한다. Lean 4에서 `V → List V` 타입.
2. **인접 행렬**(adjacency matrix)은 n×n 행렬로, (i,j)항이 1이면 인접, 0이면 비인접이다. Lean 4에서 `Fin n → Fin n → ℕ`.
3. **결합 행렬**(incidence matrix)은 n×m 행렬로, (i,j)항이 1이면 꼭지점 i가 모서리 j에 참여한다. Lean 4에서 `Fin n → Fin m → ℕ`.
4. **희박한**(sparse) 그래프에는 인접 리스트가, **촘촘한**(dense) 그래프에는 인접 행렬이 유리하다.
5. 단순 그래프의 인접 행렬은 **대칭적**이고 **대각선이 0**이다.
6. 두 그래프가 **동형**(isomorphic)이란 인접성을 보존하는 **전단사 함수**(bijection)가 존재한다는 뜻이다.
7. **그래프 불변성**(invariant) — 꼭지점 수, 모서리 수, **차수 수열**(degree sequence) — 이 다르면 비동형이다.
8. Lean 4에서 동형은 `Equiv`(전단사) + `∀ u v, G.Adj u v ↔ H.Adj (f u) (f v)`로 정의한다.
9. `fin_cases` 전술로 유한 그래프의 모든 경우를 나열하여 증명할 수 있다.

---

## 9. 사용된 Lean 4 전술 정리

| 전술/키워드 | 용도 | 예시 |
|:---|:---|:---|
| `Equiv` | 전단사 함수 정의 | `f : Fin n ≃ Fin n` |
| `Equiv.toFun` / `invFun` | 정방향/역방향 함수 | `f.toFun x`, `f.invFun y` |
| `left_inv` / `right_inv` | 역함수 관계 증명 | `f.left_inv : ∀ x, f.invFun (f x) = x` |
| `fin_cases` | `Fin n`의 모든 값 나열 | `fin_cases i <;> fin_cases j` |
| `simp_all` | 모든 가설로 단순화 | 자동 증명에 유용 |
| `Finset.filter` | 조건에 맞는 원소 필터링 | 차수 계산에 사용 |
| `List.contains` | 리스트 멤버십 확인 | 인접 리스트 탐색 |
| `mergeSort` | 리스트 정렬 | 차수 수열 비교 |

---

> **다음 파트 예고**: Part 13-F에서는 **연결성**(connectivity, Section 10.4)을 다룬다. **경로**(path), **순환**(cycle), **연결 그래프**(connected graph), **연결 요소**(connected component), **절단 꼭지점**(cut vertex), **절단 모서리**(bridge), 그리고 방향성 그래프의 **강한 연결**(strongly connected)과 **약한 연결**(weakly connected)을 배운다!
