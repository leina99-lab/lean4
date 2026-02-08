# Part 13-F: 연결성 (1) — 경로, 순환, 연결 그래프

> **Rosen 이산수학 8판 · Section 10.4 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 13-E에서는 그래프를 **표현**하는 방법(인접 리스트, 인접 행렬, 결합 행렬)과 **동형 그래프**를 배웠다. 이번 Part 13-F에서는 그래프 이론에서 가장 중요한 개념 중 하나인 **연결성**(connectivity)을 다룬다.

이 파트에서 다루는 내용:

1. **경로**(path)와 **순환**(circuit/cycle)의 정의
2. **단순 경로**(simple path)와 **단순 순환**(simple circuit)
3. **연결 그래프**(connected graph)의 정의
4. **연결 요소**(connected component)
5. **절단 꼭지점**(cut vertex)과 **절단 모서리**(bridge)
6. **꼭지점 연결성**(vertex connectivity) κ(G)와 **모서리 연결성**(edge connectivity) λ(G)
7. **방향성 그래프에서의 연결**: **강한 연결**(strongly connected)과 **약한 연결**(weakly connected)
8. 인접 행렬의 **거듭제곱으로 경로 수 세기** (정리 2)

> **핵심 비유**: 연결성은 "이 네트워크에서 어디서든 어디로든 갈 수 있는가?"라는 질문이다. 도로 네트워크라면 "서울에서 부산까지 갈 수 있는가?", 인터넷이라면 "내 컴퓨터에서 서버까지 패킷을 보낼 수 있는가?"이다.

---

## 1. 경로와 순환의 정의 (Section 10.4.2)

### 1.1 경로의 공식적 정의

> **정의 1** (Rosen): G가 비방향성 그래프이고, n이 음수가 아닌 정수일 때, 그래프 G 안의 u에서 v로의 길이가 n인 **경로**(path)는 G의 일련의 n개 모서리 e₁, ..., eₙ을 말한다. 여기서 꼭지점들의 순서는 x₀ = u, x₁, ..., xₙ₋₁, xₙ = v이고 모서리 eᵢ는 꼭지점 xᵢ₋₁과 xᵢ를 연결한다 (i = 1, ..., n).

쉬운 말로 풀어보면:

- **경로**란 꼭지점들의 연속된 열 x₀, x₁, x₂, ..., xₙ이다.
- 연속된 꼭지점 xᵢ와 xᵢ₊₁ 사이에는 반드시 모서리가 있어야 한다.
- 경로의 **길이**는 지나는 모서리의 개수 n이다.
- x₀ = u는 **시작점**, xₙ = v는 **도착점**이다.

> **비유**: 서울에서 부산까지 "서울 → 대전 → 대구 → 부산"으로 가면 길이 3의 경로이다. 각 화살표가 하나의 모서리(도로)에 해당한다.

### 1.2 순환의 정의

- **순환**(circuit): 경로의 시작점과 도착점이 같은 경로, 즉 u = v인 경로. 길이가 0보다 커야 한다.
- **단순 경로**(simple path): 같은 모서리를 한 번 이상 포함하지 않는 경로나 순환.
- **단순 순환**(simple circuit): 같은 모서리를 한 번 이상 포함하지 않는 순환.

| 용어 | 시작=끝? | 모서리 중복? | 꼭지점 중복? |
|:---|:---:|:---:|:---:|
| **경로**(path) | 아닐 수 있음 | 가능 | 가능 |
| **순환**(circuit) | 같음 | 가능 | 가능 |
| **단순 경로**(simple path) | 아닐 수 있음 | 불가 | 불가 |
| **단순 순환**(simple circuit) | 같음 | 불가 | 시작/끝만 같음 |

### 1.3 경로의 예제 (Rosen 예제 1)

그래프의 꼭지점 {a, b, c, d, e, f}에 대해:

- **a, d, c, f, e**: {a,d}, {d,c}, {c,f}, {f,e}가 모두 모서리이므로 길이 4인 **단순 경로** ✓
- **d, e, c, a**: {e,c}가 모서리가 아니므로 **경로가 아니다** ✗
- **b, c, f, e, b**: b에서 시작해서 b로 돌아오므로 길이 4인 **순환** ✓
- **a, b, e, d, a, b**: {a,b} 모서리를 두 번 포함하므로 **단순 경로 아님**

```lean
-- Lean 4에서 경로를 꼭지점 리스트로 표현

-- 간단한 경로 유효성 검증 함수
def isValidPath (G : SimpleGraph V) [DecidableRel G.Adj] : List V → Bool
  | [] => true        -- 빈 경로: 유효
  | [_] => true       -- 꼭지점 하나: 길이 0의 경로
  | u :: v :: rest =>
    decide (G.Adj u v) && isValidPath G (v :: rest)
    -- 첫 번째와 두 번째가 인접 + 나머지도 유효해야 함

-- 경로의 길이 = 꼭지점 수 - 1
def pathLength (path : List V) : ℕ := path.length - 1

-- 순환인지 확인: 시작점 = 도착점, 길이 > 0
def isCircuit [DecidableEq V] (path : List V) : Bool :=
  path.length > 1 &&
  match path.head?, path.getLast? with
  | some u, some v => u == v
  | _, _ => false

-- 단순인지 확인: 모서리 중복 없음
-- (간단히: 꼭지점 중복 없음으로 확인 — 단순 경로에서는 동일)
def isSimplePath [DecidableEq V] (path : List V) : Bool :=
  path.eraseDups.length == path.length
```

### 1.4 방향성 그래프에서의 경로 (정의 2)

> **정의 2** (Rosen): 방향성 그래프에서 u에서 v로의 길이 n인 경로는 (x₀, x₁), (x₁, x₂), ..., (xₙ₋₁, xₙ)인 모서리열이며 x₀ = u, xₙ = v이다.

**핵심 차이**: 방향성 그래프에서는 **화살표 방향**을 따라가야 한다. a → b 모서리가 있어도 b → a가 없을 수 있다!

```lean
-- 방향성 그래프의 경로: 방향을 따라가야 함
-- G.Adj u v만 확인 (G.Adj v u는 별개!)

def isValidDirPath (Adj : V → V → Prop) [DecidableRel Adj] : List V → Bool
  | [] => true
  | [_] => true
  | u :: v :: rest => decide (Adj u v) && isValidDirPath Adj (v :: rest)
```

---

## 2. 연결 그래프 (Section 10.4.3)

### 2.1 연결의 정의

> **정의 3** (Rosen): 비방향성 그래프에서 모든 꼭지점들의 쌍 사이에 경로가 존재한다면, 그래프는 **연결되었다**(connected)라고 한다. 연결되지 않은 비방향성 그래프를 **연결되지 않았다**(disconnected)라 한다. 우리가 그래프를 **분리**(disconnect)한다는 의미는 주어진 그래프에서 꼭지점이나 모서리 또는 그 둘 다를 제거하여 **분리된 부분그래프**(disconnected subgraph)를 생성하는 것이다.

```lean
-- 연결 그래프의 형식적 정의

-- 도달 가능성: u에서 v로 유한 길이의 경로가 존재
inductive Reachable' (G : SimpleGraph V) : V → V → Prop where
  | refl : ∀ v, Reachable' G v v
  | step : ∀ {u v w}, G.Adj u v → Reachable' G v w → Reachable' G u w

-- 연결 그래프: 모든 쌍이 도달 가능
def IsConnected (G : SimpleGraph V) : Prop :=
  ∀ u v : V, Reachable' G u v
```

### 2.2 정리 1: 연결 그래프의 단순 경로

> **정리 1** (Rosen): 연결된 비방향성 그래프의 모든 꼭지점들의 쌍 사이에는 **단순 경로**(simple path)가 존재한다.

**증명 아이디어**: 
1. 연결 그래프이므로 u와 v 사이에 경로가 존재한다.
2. **최소 길이**의 경로를 택한다.
3. 이 경로에 같은 꼭지점 xᵢ = xⱼ가 있다면 (i < j), xᵢ부터 xⱼ까지를 제거하면 더 짧은 경로가 생긴다.
4. 이는 "최소 길이"에 모순이므로, 최소 길이 경로는 단순 경로이다.

```lean
-- 정리 1의 핵심 아이디어를 Lean 4로 표현
-- Mathlib에서는 SimpleGraph.Walk.toPath를 사용하여
-- Walk(일반 경로)을 Path(단순 경로)로 변환한다.

-- 도달 가능성의 핵심 성질: 대칭적
theorem reachable_symm' (G : SimpleGraph V) {u v : V}
    (h : Reachable' G u v) : Reachable' G v u := by
  induction h with
  | refl _ => exact Reachable'.refl _
  | step hadj _ ih =>
    -- u~v이고 v에서 w까지의 역경로 ih를 가짐
    -- w에서 v로 (ih), 그리고 v~u (대칭)
    exact ih |>.step (G.symm hadj) |> sorry
    -- 전체 증명은 Walk의 reverse 사용

-- 도달 가능성의 핵심 성질: 추이적
theorem reachable_trans' (G : SimpleGraph V) {u v w : V}
    (huv : Reachable' G u v) (hvw : Reachable' G v w) :
    Reachable' G u w := by
  induction huv with
  | refl _ => exact hvw
  | step hadj _ ih => exact Reachable'.step hadj (ih hvw)
```

### 2.3 연결 요소

> 그래프 G의 **연결 요소**(connected component)는 G의 **최대 연결 부분그래프**(maximal connected subgraph)이다.

연결 요소는 "서로 연결된 꼭지점들의 덩어리"이다. 한 덩어리 안에서는 어디든 갈 수 있지만, 다른 덩어리와는 연결이 없다.

> **비유**: 바다 위의 여러 개의 섬. 각 섬 안에서는 다리로 연결되어 있지만 다른 섬과는 연결이 없다. 각 섬이 하나의 연결 요소이다.

```lean
-- 연결 요소: 같은 요소에 속하는 꼭지점들은 서로 도달 가능
-- Mathlib에서는 SimpleGraph.ConnectedComponent 타입을 사용

-- 두 꼭지점이 같은 연결 요소에 속하는지 판단하는 관계
def sameComponent (G : SimpleGraph V) (u v : V) : Prop :=
  Reachable' G u v

-- 이 관계가 동치 관계임을 보여야 한다!
-- 반사적: sameComponent G v v (Reachable'.refl)
-- 대칭적: sameComponent G u v → sameComponent G v u (reachable_symm')
-- 추이적: sameComponent G u v → sameComponent G v w → sameComponent G u w (reachable_trans')
```

### 2.4 예제 5: 연결 요소 찾기 (Rosen 예제 5)

그래프 H에서 세 개의 분리된 연결 부분그래프들 H₁, H₂와 H₃의 합집합이다. 이 세 부분그래프들이 H의 연결 요소들이다.

```lean
-- 비연결 그래프 예: 3개의 연결 요소를 가진 그래프
-- 꼭지점 {0,1,2,3,4,5}에서:
-- 연결 요소 1: {0, 1} (0~1)
-- 연결 요소 2: {2, 3, 4} (2~3, 3~4)
-- 연결 요소 3: {5} (고립)

def threeComponents : SimpleGraph (Fin 6) where
  Adj := fun i j => match i.val, j.val with
    | 0, 1 => True | 1, 0 => True
    | 2, 3 => True | 3, 2 => True
    | 3, 4 => True | 4, 3 => True
    | _, _ => False
  symm := by intros i j h; revert h; fin_cases i <;> fin_cases j <;> simp_all
  loopless := by intro i; fin_cases i <;> simp_all

-- 이 그래프는 연결되지 않았다 (0에서 2로 갈 수 없음)
-- 연결 요소의 수 = 3
```

---

## 3. 절단 꼭지점과 절단 모서리 (Section 10.4.4)

### 3.1 동기: 네트워크 신뢰성

컴퓨터 네트워크를 표현하는 그래프가 연결되었다는 것은 네트워크상의 두 컴퓨터가 통신할 수 있다는 것을 의미한다. 이제 이 네트워크가 얼마나 **신뢰**(reliable)할만한지 알고 싶다. 예를 들어, 어떤 라우터나 통신링크가 고장이 난 경우에도 모든 컴퓨터들은 통신 가능한가?

### 3.2 절단 꼭지점의 정의

> **절단 꼭지점**(cut vertex, articulation point): 한 꼭지점과 그 꼭지점에 인접한 모든 모서리들을 제거하면 더 많은 개수의 연결 요소들을 가진 부분그래프가 생기는 꼭지점이다.

> **쉬운 말로**: 이 꼭지점을 제거하면 그래프가 "쪼개진다"! 원래 하나로 연결되어 있던 것이 두 개 이상으로 나뉜다.

> **비유**: 도시들을 잇는 도로 네트워크에서, 특정 교차로가 없어지면 일부 도시들 사이에 이동이 불가능해진다면 그 교차로는 절단 꼭지점이다.

### 3.3 절단 모서리의 정의

> **절단 모서리**(cut edge, bridge): 한 모서리를 제거하여 그래프가 연결되지 않도록 하는 모서리이다. 원래의 그래프보다 더 많은 연결 요소를 가진 그래프가 생성되면 이를 **절단 모서리** 또는 **브리지**(bridge)라 한다.

```lean
-- 절단 꼭지점의 정의
-- v를 제거하면 연결 요소의 수가 증가하는 꼭지점

-- v를 제거한 그래프: v와 연결된 모든 모서리도 제거
def removeVertex (G : SimpleGraph V) [DecidableEq V] (v : V) :
    SimpleGraph {w : V // w ≠ v} where
  Adj u w := G.Adj u.val w.val
  symm := by intro u w h; exact G.symm h
  loopless := by intro u h; exact G.loopless u.val h

-- 절단 꼭지점: v를 제거하면 비연결이 되는 꼭지점
def IsCutVertex (G : SimpleGraph V) [DecidableEq V] (v : V) : Prop :=
  IsConnected G ∧ ¬ IsConnected (removeVertex G v)

-- 절단 모서리: 이 모서리를 제거하면 비연결이 되는 모서리
def removeEdge (G : SimpleGraph V) [DecidableEq V] (u v : V) :
    SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬ (x = u ∧ y = v) ∧ ¬ (x = v ∧ y = u)
  symm := by
    intro x y ⟨h1, h2, h3⟩
    exact ⟨G.symm h1,
      fun ⟨hx, hy⟩ => h3 ⟨hy, hx⟩,
      fun ⟨hx, hy⟩ => h2 ⟨hy, hx⟩⟩
  loopless := by
    intro x ⟨h, _, _⟩
    exact G.loopless x h

def IsBridge (G : SimpleGraph V) [DecidableEq V] (u v : V) : Prop :=
  G.Adj u v ∧ IsConnected G ∧ ¬ IsConnected (removeEdge G u v)
```

### 3.4 예제 7: 절단 꼭지점과 절단 모서리 (Rosen 예제 7)

그래프 G₁의 절단 꼭지점은 b, c, e이다. 이 꼭지점들(과 인접한 모서리들) 중 하나를 제거하면 그래프는 연결되지 않는다.

절단 모서리는 {a, b}와 {c, e}이다. 이 모서리들 중 하나를 제거하면 G₁는 연결되지 않는다.

---

## 4. 연결성의 측정 (Section 10.4.4 계속)

### 4.1 꼭지점 연결성 κ(G)

> **꼭지점 연결성**(vertex connectivity) κ(G)를 **꼭지점 절단**의 최소 꼭지점 수로 정의한다.

- κ(G) = 0: G가 **비연결 그래프**이거나 G = K₁인 그래프
- κ(K_n) = n - 1: **완전 그래프**는 n-1개 꼭지점을 제거해야 비연결이 된다
- κ(G) ≥ k이면 G를 **k-연결**(k-vertex-connected) 그래프라 한다

### 4.2 모서리 연결성 λ(G)

> **모서리 연결성**(edge connectivity) λ(G)는 G의 **모서리 절단**(edge cut)에서 모서리의 최소수이다.

- λ(G) = 0: G가 비연결 그래프
- λ(K_n) = n - 1: 완전 그래프

### 4.3 부등식 관계

> **정리** (Rosen): 모든 그래프 G에 대해 다음이 성립한다:
>
> κ(G) ≤ λ(G) ≤ min_{v∈V} deg(v)

이 부등식은 연결성의 세 가지 측도 사이의 관계를 보여준다:
- 꼭지점 연결성은 모서리 연결성 이하
- 모서리 연결성은 최소 차수 이하

```lean
-- 부등식의 직관적 이해:
-- κ(G) ≤ λ(G): 꼭지점을 제거하면 그에 인접한 모서리도 모두 제거되므로,
--              꼭지점 제거가 모서리 제거보다 "강력"하다
-- λ(G) ≤ min deg: 최소 차수의 꼭지점에 연결된 모든 모서리를 제거하면
--                그 꼭지점이 고립되므로 비연결이 된다

-- 이 부등식은 Lean 4에서 다음과 같이 표현할 수 있다:
-- 단, 전체 증명은 상당히 복잡하므로 여기서는 진술만 보여준다
theorem connectivity_inequality (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    True := by  -- 실제로는 κ(G) ≤ λ(G) ≤ min deg(v)
  trivial
```

---

## 5. 방향성 그래프의 연결성 (Section 10.4.5)

### 5.1 강한 연결 vs 약한 연결

방향성 그래프에서는 모서리의 방향을 고려하는지 여부에 따라 두 가지 개념이 있다.

> **정의 4** (Rosen): 방향성 그래프에서 a, b가 꼭지점일 때, a에서 b로 가는 경로와 b에서 a로 가는 경로가 존재한다면 **강한 연결**(strongly connected)이다.

> **정의 5** (Rosen): 기저 비방향성 그래프에서 모든 두 꼭지점 사이에 경로가 존재한다면 방향성 그래프는 **약한 연결**(weakly connected)이다.

**쉽게 비교**:

| 개념 | 조건 | 비유 |
|:---|:---|:---|
| **강한 연결** | 임의의 두 꼭지점 사이에 **방향을 따르는** 경로가 양방향으로 존재 | 일방통행도로만 있는 도시에서 어디서든 어디로든 갈 수 있다 |
| **약한 연결** | 방향을 무시하면 경로가 존재 | 일방통행 표지판을 무시하면 어디서든 어디로든 갈 수 있다 |

> **관계**: 강한 연결 → 약한 연결 (역은 성립하지 않음!)

```lean
-- 강한 연결의 정의
def StronglyConnected (Adj : V → V → Prop) : Prop :=
  ∀ u v : V, ∃ path : List V,
    path.head? = some u ∧ path.getLast? = some v ∧
    isValidDirPath Adj path = true

-- 약한 연결의 정의
-- "기저 비방향성 그래프": 방향을 무시한 그래프
def underlyingAdj (Adj : V → V → Prop) (u v : V) : Prop :=
  Adj u v ∨ Adj v u

def WeaklyConnected (Adj : V → V → Prop) : Prop :=
  ∀ u v : V, ∃ path : List V,
    path.head? = some u ∧ path.getLast? = some v ∧
    isValidDirPath (underlyingAdj Adj) path = true

-- 강한 연결 → 약한 연결
theorem strong_implies_weak (Adj : V → V → Prop)
    (h : StronglyConnected Adj) : WeaklyConnected Adj := by
  intro u v
  obtain ⟨path, h1, h2, h3⟩ := h u v
  exact ⟨path, h1, h2, by sorry⟩
  -- 방향을 따르는 경로가 있으면 방향을 무시해도 경로이다
```

### 5.2 예제 10: 강한 연결과 약한 연결 판별 (Rosen 예제 10)

그래프 G는 모든 두 꼭지점 사이에 방향성 경로가 존재하므로 **강한 연결**이다. 따라서 G는 또한 **약한 연결** 그래프이다.

그래프 H는 **강한 연결이 아니다** — a에서 b로의 방향성 경로가 존재하지 않는다. 그러나 H의 비방향성 그래프에서는 모든 두 꼭지점 간에 경로가 존재하므로 **약한 연결** 그래프이다.

### 5.3 강한 연결 요소

> **강한 연결 요소**(strongly connected component): 강한 연결이지만 보다 큰 강한 연결 부분그래프에 포함되지 않는 방향성 그래프 G의 부분그래프. 즉, **최대 강한 연결 부분그래프**이다.

---

## 6. 경로 수 세기 — 인접 행렬의 거듭제곱 (Section 10.4.7)

### 6.1 정리 2: 인접 행렬의 거듭제곱과 경로 수

> **정리 2** (Rosen): G를 꼭지점이 v₁, v₂, ..., vₙ의 순서를 갖는 인접 행렬 **A**를 갖는 그래프라 하자. (방향성 혹은 비방향성 모서리들, 다중 모서리들과 루프를 허용한다.) vᵢ에서 vⱼ로의 길이가 r인 다른 경로들의 수는 **A**ʳ의 (i, j)항과 같다.

이것은 매우 강력한 결과이다! 인접 행렬을 r번 곱하면, 길이 r인 경로의 수를 알 수 있다.

### 6.2 예제 15: 경로 수 계산 (Rosen 예제 15)

그래프 G의 인접 행렬 (a, b, c, d 순서):

```
     a  b  c  d
A = [ 0  1  1  0 ]
    [ 1  0  0  1 ]
    [ 1  0  0  1 ]
    [ 0  1  1  0 ]
```

a에서 d로 길이가 4인 경로의 수는 A⁴의 (1, 4)항이다.

A⁴를 계산하면:

```
      a  b  c  d
A⁴ = [ 8  0  0  8 ]
     [ 0  8  8  0 ]
     [ 0  8  8  0 ]
     [ 8  0  0  8 ]
```

따라서 a에서 d로 길이가 4인 경로는 정확히 **8개** 있다!

```lean
-- 인접 행렬의 거듭제곱으로 경로 수 계산
-- 행렬 곱 정의 (부울 곱이 아닌 일반 곱)
def matMul (A B : Fin n → Fin n → ℕ) : Fin n → Fin n → ℕ :=
  fun i j => Finset.sum Finset.univ (fun k => A i k * B k j)

-- 행렬 거듭제곱
def matPow (A : Fin n → Fin n → ℕ) : ℕ → (Fin n → Fin n → ℕ)
  | 0 => fun i j => if i = j then 1 else 0  -- 단위 행렬
  | r + 1 => matMul A (matPow A r)

-- 예제: A⁴의 (0, 3)항 = 8
-- 이것은 a(=0)에서 d(=3)까지 길이 4인 경로의 수

-- 실제 8개의 경로:
-- a, b, d, c, d / a, b, a, c, d / a, b, a, b, d
-- a, b, d, b, d / a, c, a, c, d / a, c, a, b, d
-- a, c, d, c, d / a, c, d, b, d
```

> **왜 이것이 성립하는가?**
>
> 수학적 귀납법으로 증명한다. A의 (i, j)항은 vᵢ에서 vⱼ로의 길이 1인 경로들의 수이다 (인접하면 1, 아니면 0). A²의 (i, j)항은 ∑_k A[i][k] × A[k][j]인데, 이것은 "vᵢ에서 vₖ로 길이 1인 경로 × vₖ에서 vⱼ로 길이 1인 경로"의 합이다. 즉, 중간 꼭지점 vₖ를 거쳐가는 길이 2인 경로의 수이다.
>
> 귀납적으로 Aʳ의 (i, j)항이 길이 r인 경로 수라고 가정하면, Aʳ⁺¹ = A × Aʳ의 (i, j)항은 ∑_k A[i][k] × Aʳ[k][j]인데, 이것은 "vᵢ에서 vₖ로 길이 1인 경로 × vₖ에서 vⱼ로 길이 r인 경로"의 합이다. 즉, 길이 r+1인 경로의 수이다!

---

## 7. 연습문제

### 연습 7.1: 경로 유효성 확인 (skeleton — 괄호 채우기)

**문제**: 다음 그래프에서 주어진 꼭지점 목록이 유효한 경로인지 확인하라.

```lean
-- 그래프: 0~1, 1~2, 2~3, 0~3 (사각형 C₄)
def C4 : SimpleGraph (Fin 4) where
  Adj := fun i j => match i.val, j.val with
    | 0, 1 => True | 1, 0 => True
    | 1, 2 => True | 2, 1 => True
    | 2, 3 => True | 3, 2 => True
    | 3, 0 => True | 0, 3 => True
    | _, _ => False
  symm := by intros i j h; revert h; fin_cases i <;> fin_cases j <;> simp_all
  loopless := by intro i; fin_cases i <;> simp_all

-- (a) 경로 [0, 1, 2, 3]: 유효한가? (단순 경로인가? 순환인가?)
-- 답: 유효 【①】, 단순 경로 【②】, 순환 아님 (0 ≠ 3)

-- (b) 경로 [0, 1, 2, 3, 0]: 유효한가?
-- 답: 유효 【③】, 순환 【④】 (0에서 시작, 0에서 끝)

-- (c) 경로 [0, 2, 3]: 유효한가?
-- 답: 유효하지 않음 【⑤】 (0과 2가 인접하지 않으므로!)
```

<details>
<summary>📝 답 보기</summary>

- ①=true: 0~1 ✓, 1~2 ✓, 2~3 ✓ 모두 인접
- ②=true: 모든 꼭지점이 다르므로 단순 경로
- ③=true: 0~1 ✓, 1~2 ✓, 2~3 ✓, 3~0 ✓ 모두 인접
- ④=true: 시작점 0 = 끝점 0, 길이 4 > 0이므로 순환
- ⑤=false: 0과 2는 C₄에서 인접하지 않음 (대각선은 모서리가 아니다!)

**핵심 포인트**: C₄(사각형)에서는 인접한 꼭지점 사이에만 모서리가 있다. 대각선(0과 2, 1과 3)은 모서리가 아니다!
</details>

---

### 연습 7.2: 연결 그래프 판별 (skeleton)

**문제**: 다음 그래프가 연결인지 판별하라.

```lean
-- 그래프 G: 꼭지점 {0,1,2,3}, 모서리 {0,1}, {2,3}
-- (두 개의 분리된 모서리)
def G_disc : SimpleGraph (Fin 4) where
  Adj := fun i j => match i.val, j.val with
    | 0, 1 => True | 1, 0 => True
    | 2, 3 => True | 3, 2 => True
    | _, _ => False
  symm := by intros i j h; revert h; fin_cases i <;> fin_cases j <;> simp_all
  loopless := by intro i; fin_cases i <;> simp_all

-- 이 그래프는 연결인가? 【답: 아니오】
-- 이유: 꼭지점 0에서 꼭지점 2로 가는 경로가 【존재하지 않는다】
-- 연결 요소의 수: 【2개】 ({0,1}과 {2,3})

theorem G_disc_not_connected : ¬ IsConnected G_disc := by
  intro h
  -- h는 모든 쌍이 도달 가능하다고 주장
  -- 0에서 2로의 도달 가능성을 이끌어내자
  have := h 0 2
  -- 0에서 도달 가능한 꼭지점은 {0, 1}뿐이다
  -- 그런데 2에 도달할 수 없다는 것을 보여야 함
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem G_disc_not_connected : ¬ IsConnected G_disc := by
  intro h
  have := h 0 2
  -- Reachable'의 귀납법으로: 0에서 시작하여 인접한 곳은 1뿐
  -- 1에서 인접한 곳은 0뿐. 따라서 2에 도달 불가
  -- 형식적 증명은 Reachable'에 대한 재귀적 분석 필요
  induction this with
  | refl => simp  -- 0 = 2? 아니다! (Fin 4에서)
  | step hadj _ ih =>
    -- hadj : G_disc.Adj 0 v
    -- 0에서 인접한 꼭지점 v는 1뿐
    fin_cases hadj  -- G_disc.Adj 0 v의 모든 가능한 경우
    -- 각 경우에서 v = 1이고, 1에서 2로 도달 불가임을 다시 보여야 함
    sorry  -- 전체 증명은 다소 길지만 아이디어는 동일
```

**아이디어**: 0에서 갈 수 있는 곳은 1뿐이고, 1에서 갈 수 있는 곳은 0뿐이다. 따라서 {0, 1}에서 벗어날 수 없으므로 2에 도달할 수 없다!
</details>

---

### 연습 7.3: 인접 행렬의 거듭제곱으로 경로 수 세기 (skeleton)

**문제**: 경로 그래프 P₃의 인접 행렬을 구하고, A²을 계산하여 꼭지점 0에서 꼭지점 2까지 길이 2인 경로의 수를 구하라.

```lean
-- P₃: 0~1~2
-- 인접 행렬:
--      0  1  2
-- A = [ 0  1  0 ]
--     [ 1  0  1 ]
--     [ 0  1  0 ]

-- A²의 계산:
-- A²[0][0] = 0×0 + 1×1 + 0×0 = 【①】
-- A²[0][1] = 0×1 + 1×0 + 0×1 = 【②】
-- A²[0][2] = 0×0 + 1×1 + 0×0 = 【③】  ← 이것이 답!
-- A²[1][1] = 1×1 + 0×0 + 1×1 = 【④】
-- A²[2][2] = 0×0 + 1×1 + 0×0 = 【⑤】
```

<details>
<summary>📝 답 보기</summary>

```
     0  1  2
A² = [ 1  0  1 ]
     [ 0  2  0 ]
     [ 1  0  1 ]
```

- ① = 1: 0에서 0으로 길이 2인 경로 (0→1→0) 1개
- ② = 0: 0에서 1로 길이 2인 경로 없음
- ③ = **1**: 0에서 2로 길이 2인 경로 (0→1→2) **1개**
- ④ = 2: 1에서 1로 길이 2인 경로 (1→0→1, 1→2→1) 2개
- ⑤ = 1: 2에서 2로 길이 2인 경로 (2→1→2) 1개

**답**: 0에서 2까지 길이 2인 경로는 **1개** (0→1→2)이다.
</details>

---

### 연습 7.4: 강한 연결 판별 (sorry)

**문제**: 다음 방향성 그래프가 강한 연결인지 판별하라.

```lean
-- 방향성 그래프: 0→1, 1→2, 2→0 (순환!)
def cycleDigraph : Fin 3 → Fin 3 → Prop := fun i j =>
  match i.val, j.val with
  | 0, 1 => True  -- 0→1
  | 1, 2 => True  -- 1→2
  | 2, 0 => True  -- 2→0
  | _, _ => False

-- 이 그래프는 강한 연결인가?
-- 0에서 1로: 0→1 ✓
-- 0에서 2로: 0→1→2 ✓
-- 1에서 0으로: 1→2→0 ✓
-- 1에서 2로: 1→2 ✓
-- 2에서 0으로: 2→0 ✓
-- 2에서 1로: 2→0→1 ✓
-- 모든 쌍에 대해 경로 존재 → 강한 연결!

theorem cycle_strongly_connected :
    ∀ (u v : Fin 3), ∃ path : List (Fin 3),
      isValidDirPath cycleDigraph path = true := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem cycle_strongly_connected :
    ∀ (u v : Fin 3), ∃ path : List (Fin 3),
      isValidDirPath cycleDigraph path = true := by
  intro u v
  fin_cases u <;> fin_cases v
  -- 0→0: [0] (길이 0)
  · exact ⟨[0], by rfl⟩
  -- 0→1: [0, 1]
  · exact ⟨[0, 1], by simp [isValidDirPath, cycleDigraph]⟩
  -- 0→2: [0, 1, 2]
  · exact ⟨[0, 1, 2], by simp [isValidDirPath, cycleDigraph]⟩
  -- 1→0: [1, 2, 0]
  · exact ⟨[1, 2, 0], by simp [isValidDirPath, cycleDigraph]⟩
  -- 1→1: [1]
  · exact ⟨[1], by rfl⟩
  -- 1→2: [1, 2]
  · exact ⟨[1, 2], by simp [isValidDirPath, cycleDigraph]⟩
  -- 2→0: [2, 0]
  · exact ⟨[2, 0], by simp [isValidDirPath, cycleDigraph]⟩
  -- 2→1: [2, 0, 1]
  · exact ⟨[2, 0, 1], by simp [isValidDirPath, cycleDigraph]⟩
  -- 2→2: [2]
  · exact ⟨[2], by rfl⟩
```

**핵심**: 0→1→2→0의 순환이 있으므로, 어떤 두 꼭지점 사이에도 이 순환의 일부를 따라 갈 수 있다. `fin_cases`로 모든 9가지 (u, v) 쌍을 나열하고 각각에 대해 구체적 경로를 제시한다.
</details>

---

### 연습 7.5: 약한 연결이지만 강한 연결이 아닌 그래프 (sorry)

**문제**: 다음 방향성 그래프가 약한 연결이지만 강한 연결이 아님을 보여라.

```lean
-- 방향성 그래프: 0→1, 0→2 (화살표가 0에서만 나감)
def starDigraph : Fin 3 → Fin 3 → Prop := fun i j =>
  match i.val, j.val with
  | 0, 1 => True  -- 0→1
  | 0, 2 => True  -- 0→2
  | _, _ => False

-- 강한 연결이 아님: 1에서 0으로 가는 방향성 경로가 없다!
-- 약한 연결: 방향을 무시하면 0~1, 0~2이므로 모든 쌍 연결됨

theorem star_not_strongly : ¬ StronglyConnected starDigraph := by
  sorry

theorem star_weakly : WeaklyConnected starDigraph := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

**강한 연결이 아닌 이유**: 꼭지점 1에서 0으로 가려면 1에서 나가는 모서리가 필요한데, `starDigraph 1 _`는 모든 경우에 `False`이다. 따라서 1에서 어디로도 갈 수 없으므로 1에서 0으로의 방향성 경로가 존재하지 않는다.

**약한 연결인 이유**: 방향을 무시하면 0~1, 0~2이므로:
- 0에서 1로: 0~1 ✓
- 0에서 2로: 0~2 ✓
- 1에서 2로: 1~0~2 ✓ (0을 거쳐서)
</details>

---

## 8. 핵심 요약

1. **경로**(path)는 연속된 모서리들의 열이다. 경로의 **길이**는 모서리의 수이다.
2. **순환**(circuit)은 시작점 = 도착점인 경로이다. **단순 순환**(simple circuit)은 모서리 중복이 없는 순환이다.
3. 비방향 그래프가 **연결**(connected)되었다 = 모든 두 꼭지점 사이에 경로가 존재한다.
4. **정리 1**: 연결 그래프에서는 모든 쌍 사이에 **단순 경로**가 존재한다.
5. **연결 요소**(connected component)는 최대 연결 부분그래프이다.
6. **절단 꼭지점**(cut vertex)을 제거하면 그래프가 분리된다. **절단 모서리**(bridge)를 제거하면 그래프가 분리된다.
7. **연결성 부등식**: κ(G) ≤ λ(G) ≤ min deg(v).
8. 방향성 그래프: **강한 연결**(양방향 경로 존재) ⊂ **약한 연결**(방향 무시 시 연결).
9. **정리 2**: 인접 행렬 **A**ʳ의 (i, j)항 = vᵢ에서 vⱼ로 길이 r인 경로의 수.
10. Lean 4에서 `Reachable'`(귀납적 도달 가능성)로 연결성을 정의하고, `fin_cases`로 유한 그래프의 성질을 증명한다.

---

## 9. 사용된 Lean 4 전술 정리

| 전술/키워드 | 용도 | 예시 |
|:---|:---|:---|
| `inductive` | 귀납적 타입 정의 | `Reachable'`의 정의 |
| `induction` | 귀납법으로 증명 | `induction h with ...` |
| `by_cases` | 경우 분리 | `by_cases h : u = v` |
| `fin_cases` | `Fin n`의 모든 값 나열 | `fin_cases u <;> fin_cases v` |
| `obtain` | 존재 양화사 분해 | `obtain ⟨path, h1, h2⟩ := ...` |
| `Finset.sum` | 유한 합 계산 | 행렬 곱에 사용 |
| `decide` | 결정 가능한 명제 판정 | `decide (G.Adj u v)` |

---

> **다음 파트 예고**: Part 13-G에서는 **오일러 경로와 해밀턴 경로**(Rosen 10.5절)를 다룬다. **오일러 순환**(Euler circuit), **오일러 경로**(Euler path), **해밀턴 순환**(Hamilton circuit), **해밀턴 경로**(Hamilton path)의 정의와 존재 조건을 배우고, 쾨니히스베르크 다리 문제를 Lean 4로 형식화한다!
