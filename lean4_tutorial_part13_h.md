# Part 13-H: 해밀턴 경로와 해밀턴 순환 — 모든 도시를 딱 한 번만 방문하기

> **Rosen 이산수학 8판 · Section 10.5.3 ~ 10.5.4 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 오일러 vs 해밀턴

Part 13-G에서는 **오일러 경로/순환** — "모든 **모서리**(edge)를 딱 한 번씩 지나기"를 배웠다. 이번 Part 13-H에서는 **해밀턴 경로/순환** — "모든 **꼭지점**(vertex)을 딱 한 번씩 방문하기"를 배운다.

| | 오일러 (Part 13-G) | 해밀턴 (이번 파트) |
|:---|:---|:---|
| **대상** | **모서리**(edge) | **꼭지점**(vertex) |
| **조건** | 모든 모서리를 한 번씩 | 모든 꼭지점을 한 번씩 |
| **판별** | 간단! (차수만 확인) | 어렵다! (NP-완전) |
| **필요충분조건** | 있음 (정리 1, 2) | 알려져 있지 않음 |
| **충분조건** | — | 디락, 오레 정리 |
| **알고리즘** | 효율적 $O(m)$ | 비효율적 (지수 시간) |

> **비유**: 
> - 오일러: "모든 **도로**를 한 번씩 달리기" 🛣️
> - 해밀턴: "모든 **도시**를 한 번씩 방문하기" 🏙️

이 파트에서 다루는 내용:

1. **해밀턴 경로**(Hamilton path)와 **해밀턴 순환**(Hamilton circuit)의 정의
2. 해밀턴 순환이 **존재하지 않음**을 보이는 기법
3. **디락 정리**(Dirac's theorem): 충분조건
4. **오레 정리**(Ore's theorem): 더 일반적인 충분조건
5. **그레이 코드**(Gray code)와 해밀턴 순환의 응용
6. **순회 외판원 문제**(TSP)
7. Lean 4에서 해밀턴 경로/순환 형식화

---

## 1. 해밀턴 경로와 해밀턴 순환의 정의

### 1.1 정의

> **정의 2** (Rosen 10.5, Definition 2)
>
> 그래프 $G$에서 **모든 꼭지점**을 **정확히 한 번씩만** 지나는 **단순 경로**를 **해밀턴 경로**(Hamilton path)라 한다.
>
> **모든 꼭지점**을 **정확히 한 번씩만** 지나는 **단순 순환**을 **해밀턴 순환**(Hamilton circuit)이라 한다.

좀 더 엄밀하게:

- 그래프 $G = (V, E)$에서 $V = \{x_0, x_1, \ldots, x_n\}$이고 $x_i \neq x_j$ ($0 \le i < j \le n$)이면, 경로 $x_0, x_1, \ldots, x_n$을 **해밀턴 경로**라 한다.
- 같은 조건에서 $x_0, x_1, \ldots, x_n, x_0$이 **해밀턴 순환**이다 ($n > 0$).

### 1.2 역사적 배경: 해밀턴의 세계일주 퍼즐

이 용어는 1857년 아일랜드 수학자 **윌리엄 로완 해밀턴**(William Rowan Hamilton, 1805~1865)에 의해 발명된 **아이코시안**(Icosian) 퍼즐에서 유래하였다. 정12면체(dodecahedron)의 20개 꼭지점에 세계의 도시 이름을 붙이고, 19개의 다른 도시를 정확히 한 번씩만 방문하고 처음 도시로 돌아오는 경로를 찾는 것이었다.

---

## 2. 해밀턴 순환의 예제

### 2.1 예제 5: 단순 그래프에서 해밀턴 순환 찾기

**그래프 G₁** (5꼭지점, 모든 쌍 연결):
```
      a
     /│╲
    / │  ╲
   e──┼───b
    ╲ │  ╱
     ╲│╱
      d ── c
```

G₁은 해밀턴 순환 a, b, c, d, e, a를 가진다. ✅

**그래프 G₂** (4꼭지점):
```
    a ── b
    │    │
    d ── c
```

해밀턴 **순환**: a, b, c, d, a ✅ (이것은 $C_4$이다.)

**그래프 G₃** (경로 그래프):
```
    a ── b ── g
    │    │
    d ── c ── e ── f
```

해밀턴 경로도 순환도 존재하지 않는다 (구조적으로 모든 꼭지점을 한 번씩 방문하는 것이 불가능).

### 2.2 해밀턴 순환이 어려운 이유

오일러 문제와 달리, 해밀턴 순환의 존재를 판별하는 **효율적인 알고리즘이 알려져 있지 않다**!

- 오일러: 차수만 세면 됨 → $O(m)$ 시간 ⚡
- 해밀턴: 최악의 경우 모든 가능한 순열을 확인해야 함 → $O(n!)$ 시간 🐌

이 문제는 **NP-완전**(NP-complete)이다. 간단히 말하면, "답이 주어지면 빠르게 검증할 수 있지만, 답을 찾는 것은 (아마도) 느리다"는 뜻이다.

---

## 3. 해밀턴 순환이 존재하지 않음을 보이는 기법

### 3.1 차수 1인 꼭지점

차수가 1인 꼭지점이 있으면 해밀턴 **순환**은 불가능하다. 해밀턴 순환에서 각 꼭지점은 정확히 2개의 모서리(들어오는 것, 나가는 것)와 인접해야 하는데, 차수 1이면 모서리가 1개뿐이다.

### 3.2 차수 2인 꼭지점의 제약

꼭지점 $v$의 차수가 2이면, $v$에 인접한 2개의 모서리는 **반드시** 해밀턴 순환의 일부여야 한다.

### 3.3 예제 6: 해밀턴 순환이 없음을 증명하기

```
    그래프 G:        그래프 H:
    a ─ d ─ e       a ─── d
    │   │           │╲  ╱│
    b ─ c           │  c  │
                    │╱  ╲│
                    b ─── e
```

**그래프 G**: 꼭지점 $e$의 차수가 1 → 해밀턴 순환 ❌

**그래프 H**: a, b, d, e의 차수가 모두 2이므로 인접한 모든 모서리가 순환에 포함되어야 함. 그러면 꼭지점 $c$의 4개 모서리를 모두 사용해야 하는데, 해밀턴 순환에서 각 꼭지점은 정확히 2개만 허용 → **불가능** ❌

---

## 4. 해밀턴 순환의 충분조건

### 4.1 디락 정리 (Dirac's Theorem, 1952)

> **정리 3** (디락 정리)
>
> $n$ ($n \ge 3$)개의 꼭지점을 갖는 **단순 그래프** $G$의 **모든 꼭지점의 차수가 최소 $n/2$**이면, $G$는 **해밀턴 순환**을 가진다.

**예시**:
- $K_5$: 차수 = 4 ≥ 5/2 = 2.5 ✅ → 해밀턴 순환 존재
- $C_5$: 차수 = 2 < 2.5 ❌ → 디락 정리 적용 불가 (하지만 해밀턴 순환은 존재!)

> ⚠️ **주의**: 디락 정리는 **충분조건**이지 필요조건이 아니다!

### 4.2 오레 정리 (Ore's Theorem, 1960)

> **정리 4** (오레 정리)
>
> $n$ ($n \ge 3$)개의 꼭지점을 갖는 단순 그래프 $G$가 **모든 비인접 꼭지점 쌍** $u$와 $v$에 대하여 $\deg(u) + \deg(v) \ge n$이면, $G$는 **해밀턴 순환**을 가진다.

디락 조건(모든 차수 ≥ n/2)이 만족되면 오레 조건도 자동 만족된다. 따라서 오레 정리가 더 일반적이다.

### 4.3 Lean 4에서 디락/오레 정리 표현

```lean
-- 디락 정리
theorem dirac_theorem 
    (n : Nat) (hn : n ≥ 3)
    (G : SimpleGraph (Fin n))
    (hG : G.Connected)
    (hdeg : ∀ v : Fin n, G.degree v ≥ n / 2) :
    hasHamiltonCycle G := by
  sorry  -- 증명은 매우 길고 복잡하다

-- 오레 정리
theorem ore_theorem
    (n : Nat) (hn : n ≥ 3)  
    (G : SimpleGraph (Fin n))
    (hG : G.Connected)
    (hore : ∀ u v : Fin n, ¬ G.Adj u v → u ≠ v → 
            G.degree u + G.degree v ≥ n) :
    hasHamiltonCycle G := by
  sorry
```

---

## 5. 해밀턴 순환의 응용

### 5.1 그레이 코드 (Gray Code) — 예제 8

**그레이 코드**(Gray code)는 인접한 코드 사이에 **딱 한 비트만** 다른 이진 코드 배열이다.

**용도**: 회전 포인터의 위치를 디지털로 표현할 때, 경계에서의 오류를 최소화한다.

**예**: 3비트 그레이 코드:
```
000 → 001 → 011 → 010 → 110 → 111 → 101 → 100 → (000으로 돌아옴)
```

이것은 **$Q_3$ (3차원 하이퍼큐브)의 해밀턴 순환**과 동일하다!

- $Q_n$의 꼭지점: 길이 $n$인 모든 이진 문자열
- $Q_n$의 모서리: 한 비트만 다른 두 문자열을 연결
- 그레이 코드 = $Q_n$의 해밀턴 순환

### 5.2 Lean 4에서 하이퍼큐브와 그레이 코드

```lean
-- n-큐브 Qₙ 정의
def hypercube (n : Nat) : SimpleGraph (Fin n → Bool) where
  Adj u v := (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm := by
    intro u v h
    convert h using 1
    ext i; constructor <;> exact Ne.symm
  loopless := by intro v h; simp at h

-- 3비트 그레이 코드
def grayCode3 : List (Fin 3 → Bool) := [
  ![false, false, false],  -- 000
  ![false, false, true],   -- 001
  ![false, true,  true],   -- 011
  ![false, true,  false],  -- 010
  ![true,  true,  false],  -- 110
  ![true,  true,  true],   -- 111
  ![true,  false, true],   -- 101
  ![true,  false, false]   -- 100
]
```

### 5.3 순회 외판원 문제 (TSP)

**순회 외판원 문제**(Traveling Salesman Problem, TSP)는 가장 유명한 최적화 문제이다.

> **문제**: 외판원이 $n$개의 도시를 **정확히 한 번씩** 방문하고 **출발점으로 돌아오는** 경로 중 **가장 짧은** 경로를 찾아라.

이것은 **가중치 완전 그래프**에서 **최소 가중치 해밀턴 순환**을 찾는 문제이다.

모든 가능한 순환 수: $(n-1)!/2$. $n = 25$이면 약 $3.1 \times 10^{23}$개!

```lean
-- TSP를 위한 가중치 완전 그래프
structure TSPInstance (n : Nat) where
  dist : Fin n → Fin n → Nat
  dist_symm : ∀ i j, dist i j = dist j i
  dist_zero : ∀ i, dist i i = 0

-- 순환의 총 비용 계산
def tourCost {n : Nat} (inst : TSPInstance n) (tour : List (Fin n)) : Nat :=
  match tour with
  | [] => 0
  | [_] => 0
  | x :: y :: rest => inst.dist x y + tourCost inst (y :: rest)
```

---

## 6. Lean 4에서 해밀턴 경로/순환 형식화

### 6.1 해밀턴 경로의 정의

```lean
-- 해밀턴 경로: 모든 꼭지점을 정확히 한 번 방문하는 경로
structure HamiltonPath (G : SimpleGraph (Fin n)) where
  path : List (Fin n)
  all_vertices : ∀ v : Fin n, v ∈ path
  no_duplicates : path.Nodup
  adjacent : ∀ i, i + 1 < path.length → 
    G.Adj (path.get ⟨i, by omega⟩) (path.get ⟨i + 1, by omega⟩)

-- 해밀턴 순환: 해밀턴 경로 + 마지막과 처음이 인접
structure HamiltonCycle (G : SimpleGraph (Fin n)) extends HamiltonPath G where
  closes : path.length > 0 → 
    G.Adj (path.getLast (by sorry)) (path.head (by sorry))
```

### 6.2 완전 그래프 Kₙ은 항상 해밀턴 순환을 가진다 (예제 7)

```lean
-- n ≥ 3일 때 Kₙ은 해밀턴 순환을 가진다.
-- 증명: 0, 1, 2, ..., n-1, 0 순서로 방문하면 된다.

def completeGraph (n : Nat) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v
  symm := by intro u v h; exact Ne.symm h
  loopless := by intro v h; exact absurd rfl h

-- K₄의 해밀턴 순환: 0 → 1 → 2 → 3 → 0
example : (completeGraph 4).Adj (0 : Fin 4) (1 : Fin 4) := by decide
```

---

## 7. 연습문제

### 연습 7.1: 해밀턴 순환 존재 판별 (괄호 채우기)

```
-- (a) K₆ (완전 그래프, 6꼭지점)
--     해밀턴 순환: 【       】 (답: 존재)

-- (b) C₅ (5-순환)
--     해밀턴 순환: 【       】 (답: 존재)
--     경로의 예: 0 → 【  】→ 【  】→ 【  】→ 【  】→ 0  (답: 1,2,3,4)

-- (c) Petersen 그래프 (10꼭지점, 차수=3)
--     해밀턴 순환: 【       】 (답: 존재하지 않음!)

-- (d) K₃,₃ (완전 이분 그래프)
--     해밀턴 순환: 【       】 (답: 존재)

-- (e) K₂,₃ (완전 이분 그래프)
--     해밀턴 순환: 【       】 (답: 존재하지 않음)
--     이유: 이분 그래프에서 순환은 양쪽을 번갈아 방문 → 양쪽 수가 같아야 함
--     해밀턴 경로: 【       】 (답: 존재)
```

<details>
<summary>📝 답 보기</summary>

```
(a) K₆: 존재 ✅ (완전 그래프, n≥3)
(b) C₅: 존재 ✅ (순환 자체가 해밀턴 순환) 경로: 0→1→2→3→4→0
(c) Petersen: 존재하지 않음 ❌ (유명한 결과)
(d) K₃,₃: 존재 ✅ (양쪽 각 3개로 같음)
(e) K₂,₃: 순환 ❌ (2≠3), 경로 ✅
```

</details>

---

### 연습 7.2: 디락 정리 적용 (괄호 채우기)

```
-- 디락 정리: n ≥ 3이고 모든 차수 ≥ n/2이면 해밀턴 순환 존재

-- (a) n = 6, 모든 차수 ≥ 3
--     n/2 = 【    】 (답: 3)
--     디락 조건 만족? 【       】 (답: 만족)
--     결론: 【       】 (답: 해밀턴 순환 존재)

-- (b) n = 10, 모든 차수 ≥ 4
--     n/2 = 【    】 (답: 5)
--     디락 조건 만족? 【       】 (답: 불만족 (4 < 5))
--     결론: 【       】 (답: 디락 정리로는 판단 불가)

-- (c) n = 7, 모든 차수 ≥ 4
--     n/2 = 【      】 (답: 3.5)
--     디락 조건 만족? 【       】 (답: 만족 (4 ≥ 3.5))
--     결론: 【       】 (답: 해밀턴 순환 존재)

-- (d) K₅,₅ (10꼭지점, 모든 차수 = 5)
--     n/2 = 【    】 (답: 5)
--     디락 조건 만족? 【       】 (답: 만족 (5 ≥ 5))
```

<details>
<summary>📝 답 보기</summary>

```
(a) n=6, 차수≥3: n/2=3, 만족 → 해밀턴 순환 ✅
(b) n=10, 차수≥4: n/2=5, 불만족 → 판단 불가 ⚠️
(c) n=7, 차수≥4: n/2=3.5, 만족 → 해밀턴 순환 ✅
(d) K₅,₅: n=10, 차수=5, n/2=5, 만족 → 해밀턴 순환 ✅
```

</details>

---

### 연습 7.3: 오레 정리 vs 디락 정리 (괄호 채우기)

```
-- 오레 정리: 모든 비인접 쌍 u,v에 대해 deg(u) + deg(v) ≥ n이면 해밀턴 순환

-- "디락 조건이 만족되면 오레 조건도 만족된다"를 증명하라:
-- 디락: ∀ v, deg(v) ≥ n/2
-- 비인접 쌍 u,v에 대해:
-- deg(u) + deg(v) ≥ 【    】 + 【    】 = 【    】 ≥ n  (답: n/2, n/2, n)
-- 따라서 오레 조건 만족 ✅

-- 이것을 Lean 4로:
-- ∀ v, deg(v) ≥ n/2 → ∀ u v, ¬Adj u v → deg(u) + deg(v) ≥ n
-- 이것은 【    】→ (if)의 관계이다 (답: →)
-- 디락 ↔ 오레 인가? 【    】 (답: 아니다! 디락 → 오레이지만, 오레 → 디락은 아니다)
```

<details>
<summary>📝 답 보기</summary>

```
디락 → 오레 증명:
deg(u) ≥ n/2 이고 deg(v) ≥ n/2 이므로
deg(u) + deg(v) ≥ n/2 + n/2 = n ✅

디락 → 오레 (한 방향)
오레 → 디락은 성립하지 않음 (오레가 더 일반적)
```

</details>

---

### 연습 7.4: Lean 4로 해밀턴 판별 함수 작성 (skeleton)

```lean
-- 해밀턴 순환 존재 여부를 나타내는 명제
def hasHamiltonCycle (G : SimpleGraph (Fin n)) : Prop :=
  ∃ path : List (Fin n),
    path.Nodup ∧
    path.length = n ∧
    (∀ v : Fin n, v ∈ path) ∧
    (∀ i, i + 1 < path.length → 
      G.Adj (path.get ⟨i, by omega⟩) (path.get ⟨i+1, by omega⟩)) ∧
    (path.length > 1 → 
      G.Adj (path.getLast 【          】) (path.head 【          】))
      -- (답: (by sorry), (by sorry))
```

<details>
<summary>📝 답 보기</summary>

```lean
def hasHamiltonCycle (G : SimpleGraph (Fin n)) : Prop :=
  ∃ path : List (Fin n),
    path.Nodup ∧
    path.length = n ∧
    (∀ v : Fin n, v ∈ path) ∧
    (∀ i, i + 1 < path.length → 
      G.Adj (path.get ⟨i, by omega⟩) (path.get ⟨i+1, by omega⟩)) ∧
    (path.length > 1 → 
      G.Adj (path.getLast (by sorry)) (path.head (by sorry)))
```

</details>

---

### 연습 7.5: 그레이 코드 검증 (skeleton)

```lean
-- 2비트 그레이 코드가 Q₂의 해밀턴 순환인지 검증

def gray2 : List (Fin 2 → Bool) := [
  ![false, false],  -- 00
  ![false, true],   -- 01
  ![true,  true],   -- 11
  ![true,  false]   -- 10
]

-- 인접한 쌍이 정확히 한 비트만 다른지 확인하는 함수
def differByOneBit (a b : Fin 2 → Bool) : Bool :=
  (Finset.univ.filter (fun i => a i ≠ b i)).card = 【    】  -- (답: 1)

-- 순환 검증: 모든 연속 쌍 + 마지막↔처음이 한 비트만 다른지
def isGrayCodeCycle (code : List (Fin 2 → Bool)) : Bool :=
  -- 연속 쌍 확인 + 마지막과 처음 확인
  match code.head?, code.getLast? with
  | some h, some t => differByOneBit 【    】 【    】  -- (답: t, h)
  | _, _ => false
```

<details>
<summary>📝 답 보기</summary>

```lean
def differByOneBit (a b : Fin 2 → Bool) : Bool :=
  (Finset.univ.filter (fun i => a i ≠ b i)).card = 1

def isGrayCodeCycle (code : List (Fin 2 → Bool)) : Bool :=
  match code.head?, code.getLast? with
  | some h, some t => differByOneBit t h
  | _, _ => false
```

</details>

---

### 연습 7.6: 오일러 vs 해밀턴 종합 비교 (괄호 채우기)

```
-- 다음 그래프에서 오일러와 해밀턴의 존재 여부를 모두 판별하라.

-- (a) K₅ (완전 그래프, 5꼭지점, 차수=4)
--     오일러 순환: 【    】 (답: ✅, 차수 짝수)
--     해밀턴 순환: 【    】 (답: ✅, 완전 그래프)

-- (b) K₄ (완전 그래프, 4꼭지점, 차수=3)
--     오일러 순환: 【    】 (답: ❌, 차수 홀수)
--     해밀턴 순환: 【    】 (답: ✅, 완전 그래프)

-- (c) C₆ (6-순환, 차수=2)
--     오일러 순환: 【    】 (답: ✅, 차수 짝수)
--     해밀턴 순환: 【    】 (답: ✅, 순환=해밀턴 순환)

-- (d) Petersen 그래프 (10꼭지점, 차수=3)
--     오일러 순환: 【    】 (답: ❌, 차수 홀수)
--     해밀턴 순환: 【    】 (답: ❌)

-- 일반 규칙:
-- Kₙ (n≥3): n 홀수 → 오일러✅+해밀턴✅, n 짝수 → 오일러❌+해밀턴✅
-- Cₙ (n≥3): 항상 오일러✅+해밀턴✅
-- Wₙ (n≥3): 테두리 차수=3 → 오일러❌, 해밀턴【    】 (답: ✅)
```

<details>
<summary>📝 답 보기</summary>

```
(a) K₅: 오일러 ✅ (차수 4 짝수) + 해밀턴 ✅ 
(b) K₄: 오일러 ❌ (차수 3 홀수) + 해밀턴 ✅ 
(c) C₆: 오일러 ✅ (차수 2 짝수) + 해밀턴 ✅ 
(d) Petersen: 오일러 ❌ + 해밀턴 ❌ 

Kₙ: n홀수→양쪽✅, n짝수→오일러❌+해밀턴✅
Cₙ: 항상 양쪽 ✅
Wₙ: 오일러❌ (테두리 홀수), 해밀턴✅
```

</details>

---

### 연습 7.7: 차수 1인 꼭지점과 해밀턴 (sorry)

```lean
-- 경로 그래프 P₄: 0 — 1 — 2 — 3
def P4 : SimpleGraph (Fin 4) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := by intro u v h; rcases h with h | h <;> simp_all
  loopless := by intro v h; rcases h with h | h <;> omega

-- P₄에서 꼭지점 0의 차수는 1이다.
-- 따라서 해밀턴 순환은 존재하지 않는다.
theorem P4_no_hamilton_cycle : ¬ hasHamiltonCycle P4 := by
  sorry
  -- 힌트: 해밀턴 순환에서 각 꼭지점은 2개의 모서리를 사용
  -- deg(0) = 1이므로 불가능
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem P4_no_hamilton_cycle : ¬ hasHamiltonCycle P4 := by
  intro ⟨path, hnodup, hlen, hall, hadj, hclose⟩
  -- 꼭지점 0은 차수 1 → 이웃이 1뿐
  -- 해밀턴 순환에서 0의 전후 꼭지점이 모두 1이어야 함 → 중복 → 모순
  sorry
```

</details>

---

### 연습 7.8: TSP 비용 계산 (괄호 채우기)

```
-- 5개 도시 TSP
-- 0=Detroit, 1=Toledo, 2=Saginaw, 3=GrandRapids, 4=Kalamazoo

-- 순환: Detroit → Toledo → Kalamazoo → GrandRapids → Saginaw → Detroit
-- 비용: 58 + 137 + 56 + 113 + 98 = 【    】 (답: 462)

-- 가능한 순환 수: (n-1)!/2 = 【    】!/2 = 【    】/2 = 【    】 (답: 4!/2 = 24/2 = 12)
-- n=25일 때 순환 수: 24!/2 ≈ 【        】 (답: 3.1 × 10²³)
```

<details>
<summary>📝 답 보기</summary>

```
비용: 58 + 137 + 56 + 113 + 98 = 462
순환 수: (5-1)!/2 = 4!/2 = 24/2 = 12
n=25: 24!/2 ≈ 3.1 × 10²³
```

</details>

---

## 8. 핵심 요약

1. **해밀턴 경로**(Hamilton path)는 모든 **꼭지점**을 정확히 한 번 방문하는 경로이다.
2. **해밀턴 순환**(Hamilton circuit)은 모든 꼭지점을 한 번씩 방문하고 돌아오는 순환이다.
3. 해밀턴 순환의 필요충분조건은 **알려져 있지 않다** (NP-완전).
4. **디락 정리**: $n \ge 3$이고 모든 차수 $\ge n/2$이면 해밀턴 순환 존재 (충분조건).
5. **오레 정리**: 비인접 쌍 $u, v$에 대해 $\deg(u) + \deg(v) \ge n$이면 해밀턴 순환 존재 (더 일반적 충분조건).
6. 디락 조건 ⊂ 오레 조건 (디락 → 오레이지만, 오레 → 디락은 아님).
7. **그레이 코드** = $Q_n$의 해밀턴 순환.
8. **TSP** = 최소 비용 해밀턴 순환 찾기 (NP-완전).
9. $K_n$ ($n \ge 3$)은 항상 해밀턴 순환을 가진다.
10. 차수 1인 꼭지점이 있으면 해밀턴 순환 불가능.

---

## 9. 사용된 Lean 4 전술 정리

| 전술/키워드 | 용도 | 예시 |
|:---|:---|:---|
| `List.Nodup` | 리스트 중복 없음 | 꼭지점 방문 중복 방지 |
| `structure` / `extends` | 구조체 정의/상속 | `HamiltonCycle extends HamiltonPath` |
| `Equiv.Perm` | 순열 | 해밀턴 경로를 순열로 표현 |
| `fin_cases` | 유한 경우 분석 | 유한 그래프 확인 |
| `decide` | 결정 가능 명제 | `(completeGraph 4).Adj 0 1` |
| `omega` | 자연수 산술 | 인덱스 범위 |
| `match` | 패턴 매칭 | 거리 함수, 리스트 처리 |
| `sorry` | 미완성 증명 | 복잡한 증명 자리 표시 |

---

> **다음 파트 예고**: Part 13-I에서는 **최단경로 문제**(Section 10.6)를 다룬다. **다익스트라 알고리즘**(Dijkstra's algorithm)으로 가중치 그래프에서 두 꼭지점 사이의 최단경로를 찾고, **플로이드 알고리즘**(Floyd's algorithm)으로 모든 쌍의 최단경로를 구하는 방법을 Lean 4로 구현한다!
