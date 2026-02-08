# Part 13-D: 이분 그래프, 매칭, 그래프 연산 (Bipartite Graphs, Matching, Graph Operations)

> **Rosen 이산수학 8판 · Section 10.2 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 13-C에서는 그래프의 기본 용어(인접, 차수, 악수 정리)와 특수 그래프(Kₙ, Cₙ, Wₙ, Qₙ)를 배웠다. 이번 Part 13-D에서는 그래프 이론의 또 다른 핵심 주제들을 다룬다.

이 파트에서 다루는 내용:

1. **이분 그래프**(bipartite graph): 꼭지점을 두 그룹으로 나누기
2. **이분 판정** (정리 4): 2-색칠 가능성
3. **완전 이분 그래프** K_{m,n}
4. **매칭**(matching): 서로 겹치지 않는 모서리 선택
5. **홀의 결혼이론**(Hall's marriage theorem)
6. **특수 그래프의 응용**: LAN, 병렬 계산
7. **새 그래프 만들기**: 부분그래프, 모서리 추가/제거, 축약, 합집합

> **핵심 비유**: 이분 그래프는 "맞선 파티"와 같다! 남성 그룹과 여성 그룹이 있고, 모서리는 서로 관심 있는 남녀 쌍을 연결한다. 매칭은 "실제 커플 맺기"이고, 홀의 결혼이론은 "모든 남성이 결혼할 수 있는 조건"을 알려준다.

---

## 1. 이분 그래프 (Section 10.2.4)

### 1.1 이분 그래프란?

때때로 그래프의 꼭지점 집합이 두 개의 분리된 부분집합으로 나누어지고 각 모서리는 한 부분집합의 꼭지점과 다른 부분집합의 꼭지점을 연결하는 특성을 갖는 그래프가 있다.

> **정의 6** (Rosen): 단순 그래프 G에서 그 꼭지점들의 집합 V가 두 개의 겹치지 않는 집합 V₁과 V₂로 분리되고, 그래프의 모든 모서리는 V₁의 한 꼭지점과 V₂의 한 꼭지점만을 연결하면, 이 단순 그래프를 **이분 그래프**(bipartite graph)라고 한다. 이 조건이 만족되면 꼭지점 쌍 (V₁, V₂)를 G의 꼭지점집합 V의 **이분**(bipartition)이라고 한다.

쉽게 말하면:
- 꼭지점을 **두 팀**으로 나눈다 (V₁과 V₂)
- **같은 팀 내에서는 모서리가 없다** (팀원끼리는 연결 ✗)
- **모든 모서리는 팀 사이를** 연결한다 (V₁ ↔ V₂)

**비유**: 학교 운동회에서 백팀과 청팀이 있다. "악수 관계"가 이분적이라면, 백팀 학생은 청팀 학생과만 악수하고, 같은 팀 학생과는 악수하지 않는다.

```lean
-- 이분 그래프 구조체
structure BipartiteGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  side : Fin n → Bool             -- true = V₁, false = V₂
  sym : ∀ i j, adj i j = adj j i
  irr : ∀ i, adj i i = false
  bipartite : ∀ i j, adj i j = true → side i ≠ side j
```

### 1.2 예제 9 (Rosen): C₆는 이분 그래프

사이클 C₆의 꼭지점들의 집합이 두 개의 집합 V₁ = {v₁, v₃, v₅}과 V₂ = {v₂, v₄, v₆}로 나누어지고 C₆의 모든 모서리는 V₁의 한 꼭지점과 V₂의 한 꼭지점을 연결하고 있기 때문에 C₆은 이분(bipartite)이다.

```lean
-- C₆: 홀수 번 꼭지점 vs 짝수 번 꼭지점
-- V₁ = {0, 2, 4}, V₂ = {1, 3, 5}
-- 모서리: (0,1),(1,2),(2,3),(3,4),(4,5),(5,0) — 항상 홀수↔짝수 ✓
```

**일반 규칙**: 짝수 길이 사이클 C_{2k}는 항상 이분. **홀수 길이 사이클 C_{2k+1}은 이분 아님!**

### 1.3 예제 10 (Rosen): K₃는 이분이 아니다

K₃의 꼭지점 3개를 두 집합으로 나누면, 비둘기집 원리에 의해 어떤 집합에 최소 2개의 꼭지점이 들어간다. K₃에서는 그 2개 꼭지점이 모서리로 연결되어 있으므로 이분 조건 위반!

### 1.4 2-색칠 판정법 (정리 4)

> **정리 4**: 그래프가 이분 그래프일 **필요충분조건**(↔)은 두 인접한 꼭지점들이 같은 색깔을 갖지 않도록 두 개의 색으로 그래프의 모든 꼭지점들을 색칠할 수 있어야 한다.

여기서 잠깐! **필요충분조건**(↔, if and only if)이란 무엇인가?

- **→ (if, 충분조건)**: "이분이면 2-색칠 가능하다"
- **← (only if, 필요조건)**: "2-색칠 가능하면 이분이다"
- **↔ (iff)**: 양쪽 모두 성립! "이분 ⟺ 2-색칠 가능"

Lean 4에서는 `→`는 `\to`, `↔`는 `\iff`로 입력한다. `↔`는 `→`와 `←`를 모두 포함한다!

```lean
-- → vs ↔ 복습
-- h : P → Q  — P가 성립하면 Q가 성립
-- h : P ↔ Q  — P ⟺ Q (양방향)

-- ↔를 분해하기: h.mp (→ 방향), h.mpr (← 방향)
-- 또는 ⟨fun hp => ..., fun hq => ...⟩로 구성

-- 정리 4를 Lean 4로 표현하면:
-- theorem bipartite_iff_two_colorable :
--   isBipartite G ↔ isTwoColorable G := ⟨forward_proof, backward_proof⟩
```

**증명 아이디어**:
- (→) 이분이면 V₁을 빨간색, V₂를 파란색 → 인접한 꼭지점은 다른 색
- (←) 2-색칠 가능하면 빨간 집합 = V₁, 파란 집합 = V₂로 나누면 이분

**알고리즘**: BFS로 2-색칠 시도. 한 꼭지점에서 시작하여 색을 칠하고, 인접한 꼭지점에 반대 색을 칠한다. 충돌이 생기면 이분이 아니다!

---

## 2. 완전 이분 그래프 K_{m,n}

> **예제 13** (Rosen): **완전 이분 그래프**(complete bipartite graph) K_{m,n}은 꼭지점의 집합이 각각 m과 n개의 꼭지점들을 갖는 두 부분집합으로 나누어지는 그래프이다. 한 꼭지점은 첫 번째 부분집합에 속하고 다른 꼭지점은 두 번째 부분집합에 속할 때만 두 꼭지점 간에 모서리가 존재한다.

**성질**:
- 꼭지점 수: m + n, 모서리 수: m × n
- V₁쪽 차수: n, V₂쪽 차수: m
- K_{1,n}은 **성형 그래프**(star graph) — LAN의 성형 위상!

```lean
-- 완전 이분 그래프
def completeBipartite (m n : ℕ) : Fin (m + n) → Fin (m + n) → Bool :=
  fun i j => (i.val < m && j.val ≥ m) || (i.val ≥ m && j.val < m)
```

---

## 3. 매칭과 홀의 결혼이론 (Section 10.2.5)

### 3.1 매칭이란?

> 단순 그래프 G = (V, E)에서 **매칭**(matching) M은 그래프에서 두 모서리가 같은 꼭지점에 인접하지 않는 모서리들의 집합 E의 부분집합이다.

쉽게 말하면: 매칭 = **서로 겹치지 않는 모서리들의 집합**. 한 꼭지점은 최대 하나의 매칭 모서리에 참여한다.

- **최대 매칭**(maximum matching): 모서리 수가 최대인 매칭
- **완전 매칭**(complete matching): V₁의 모든 꼭지점이 매칭된 것

```lean
-- 매칭: 서로 겹치지 않는 모서리들의 집합
def isMatching (edges : List (Fin n × Fin n)) : Prop :=
  ∀ i j, i ≠ j → i < edges.length → j < edges.length →
    let (a₁, b₁) := edges[i]!
    let (a₂, b₂) := edges[j]!
    a₁ ≠ a₂ ∧ a₁ ≠ b₂ ∧ b₁ ≠ a₂ ∧ b₁ ≠ b₂
```

### 3.2 홀의 결혼이론 (정리 5)

> **정리 5**: 이분인 꼭지점 (V₁, V₂)를 갖는 이분 그래프 G = (V, E)가 V₁에서 V₂로 완전 매칭일 **필요충분조건**은 V₁의 **모든** 부분집합 A에 대해 |N(A)| ≥ |A|이다.

**쉽게 말하면**: "모든 남성이 결혼할 수 있으려면, 남성 그룹의 어떤 부분도 그들이 원하는 여성의 수 이상이어야 한다."

```lean
-- 홀의 조건
def neighborhoodSet (adj : Fin m → Fin n → Bool) (A : Finset (Fin m))
    : Finset (Fin n) :=
  Finset.univ.filter fun j => A.any fun i => adj i j

def hallCondition (adj : Fin m → Fin n → Bool) : Prop :=
  ∀ A : Finset (Fin m), A.card ≤ (neighborhoodSet adj A).card
```

### 3.3 예제 14 (Rosen): 작업 할당

**프로젝트 1** (Alvarez, Berkowitz, Chen, Davis):
- 완전 매칭 존재: Alvarez→테스트, Berkowitz→시행, Chen→건축, Davis→규정

**프로젝트 2** (Washington, Xuan, Ybarra, Ziegler):
- 완전 매칭 **불존재**: Xuan, Ziegler 둘이서 3작업을 나눌 수 없다
- 홀의 조건 위반: {Xuan, Ziegler}의 이웃 = {규정, 시행, 검사/테스트} → |N| = 3 < ... 실제로 확인 필요

---

## 4. 특수 그래프의 응용 (Section 10.2.6)

### 4.1 근거리 통신망 (LAN)

세 가지 주요 네트워크 구조:
- **성형 위상**(star topology): 모든 장치가 중앙에 연결 → K_{1,n}
- **환형 위상**(ring topology): 양쪽 이웃과 연결 → Cₙ
- **혼합형**: 성형 + 환형 → Wₙ (중복 경로로 신뢰도 향상)

### 4.2 병렬 계산 상호 연결망

- **완전 연결**: Kₙ — 빠르지만 비용 C(n,2)
- **선형 배열**: 경로 그래프 — 간단하지만 홉 많음
- **망사형**(mesh): m×m 격자 — 균형
- **하이퍼큐브**: Qₘ — 직접 연결과 홉의 균형

```lean
-- 망사형 네트워크 인접 관계
def meshAdj (m : ℕ) (p q : Fin m × Fin m) : Bool :=
  (p.1 == q.1 && (q.2.val == p.2.val + 1 || p.2.val == q.2.val + 1)) ||
  (p.2 == q.2 && (q.1.val == p.1.val + 1 || p.1.val == q.1.val + 1))
```

---

## 5. 새 그래프 만들기 (Section 10.2.7)

### 5.1 부분그래프

> **정의 7** (Rosen): 그래프 G = (V, E)의 **부분그래프**(subgraph)는 W ⊆ V이고 F ⊆ E인 그래프 H = (W, F)이다.

> **정의 8** (Rosen): **유도된 부분그래프**(induced subgraph)는 꼭지점 집합 W를 선택하면 W 내의 모든 원래 모서리가 자동 포함되는 부분그래프이다.

```lean
-- 유도된 부분그래프: 꼭지점만 선택하면 모서리는 자동 결정
def inducedSubgraph (adj : Fin n → Fin n → Bool) (W : Finset (Fin n))
    : Fin n → Fin n → Bool :=
  fun i j => adj i j && (decide (i ∈ W)) && (decide (j ∈ W))
```

### 5.2 모서리 제거와 추가

```lean
-- 모서리 제거
def removeEdge (adj : Fin n → Fin n → Bool) (u v : Fin n) : Fin n → Fin n → Bool :=
  fun i j =>
    if (i == u && j == v) || (i == v && j == u) then false
    else adj i j

-- 모서리 추가
def addEdge (adj : Fin n → Fin n → Bool) (u v : Fin n) : Fin n → Fin n → Bool :=
  fun i j =>
    if (i == u && j == v) || (i == v && j == u) then true
    else adj i j
```

### 5.3 꼭지점 제거

```lean
-- 꼭지점 제거: 해당 꼭지점과 인접 모서리 모두 제거
def removeVertex (adj : Fin n → Fin n → Bool) (v : Fin n) : Fin n → Fin n → Bool :=
  fun i j => if i == v || j == v then false else adj i j
```

### 5.4 모서리 축약

모서리 {u, v}를 제거하고 u와 v를 새 꼭지점 w로 합친다. u 또는 v의 이웃은 모두 w의 이웃이 된다.

### 5.5 그래프의 합집합

> **정의 9** (Rosen): G₁ = (V₁, E₁)과 G₂ = (V₂, E₂)의 **합집합** G₁ ∪ G₂ = (V₁ ∪ V₂, E₁ ∪ E₂)

```lean
def graphUnion (adj1 adj2 : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  fun i j => adj1 i j || adj2 i j
```

---

## 6. 연습 문제 — 레벨 1: 괄호 채우기

### 연습 6.1: 이분 그래프 판별 (Rosen 연습문제 21-25)

```
(a) C₅ (오각형) — 이분인가? /- ? -/
    이유: /- ? -/

(b) C₆ (육각형) — 이분인가? /- ? -/
    이유: /- ? -/

(c) K₃,₃ — 이분인가? /- ? -/
    이유: /- ? -/

(d) K₄ — 이분인가? /- ? -/
    이유: /- ? -/
```

<details>
<summary>💡 답 보기</summary>

```
(a) C₅: 이분 아님 ✗. 홀수 사이클 → 2-색칠 불가.
(b) C₆: 이분 ✓. 짝수 사이클 → 홀짝 번호로 분류 가능.
(c) K₃,₃: 이분 ✓. 완전 이분 그래프는 정의에 의해 이분.
(d) K₄: 이분 아님 ✗. 삼각형(K₃ 부분그래프) 포함 → 홀수 사이클 존재.
```
</details>

### 연습 6.2: 완전 이분 그래프 성질

```
| 그래프   | V₁ 크기 | V₂ 크기 | 모서리 수 | V₁ 차수 | V₂ 차수 |
|---------|--------|--------|---------|--------|--------|
| K₂,₃   | 2      | 3      | /- ? -/ | /- ? -/| /- ? -/|
| K₃,₃   | 3      | 3      | /- ? -/ | /- ? -/| /- ? -/|
| K₃,₅   | 3      | 5      | /- ? -/ | /- ? -/| /- ? -/|
| K_{m,n} | m      | n      | /- ? -/ | /- ? -/| /- ? -/|
```

<details>
<summary>💡 답 보기</summary>

```
| 그래프   | V₁ 크기 | V₂ 크기 | 모서리 수 | V₁ 차수 | V₂ 차수 |
|---------|--------|--------|---------|--------|--------|
| K₂,₃   | 2      | 3      | 6       | 3      | 2      |
| K₃,₃   | 3      | 3      | 9       | 3      | 3      |
| K₃,₅   | 3      | 5      | 15      | 5      | 3      |
| K_{m,n} | m      | n      | m×n     | n      | m      |

악수 정리 검증 (K₃,₅): Σ deg = 3×5 + 5×3 = 30 = 2×15 ✓
```
</details>

### 연습 6.3: n의 값에 따른 이분 판별 (Rosen 연습문제 26)

```
a) Kₙ이 이분이 되려면 n = /- ? -/
b) Cₙ이 이분이 되려면 n = /- ? -/
c) Wₙ이 이분이 되려면 n = /- ? -/
d) Qₙ이 이분이 되려면 n = /- ? -/
```

<details>
<summary>💡 답 보기</summary>

```
a) Kₙ: n = 1 또는 n = 2만 가능 (K₃부터 삼각형 포함)
b) Cₙ: n이 짝수일 때만 (n = 4, 6, 8, ...)
c) Wₙ: 어떤 n에서도 이분 아님 (항상 삼각형 포함)
d) Qₙ: 모든 n ≥ 1에서 이분! (1의 개수 홀짝으로 분류)
```
</details>

### 연습 6.4: 홀의 조건 검증 (Rosen 연습문제 27)

Ping: 하드웨어, 네트워킹, 무선 / Quiggley: 소프트웨어, 네트워킹 / Ruiz: 네트워킹, 무선 / Sitea: 하드웨어, 소프트웨어

```
A = {Ping}: |N| = 3 ≥ 1 ✓
A = {Quiggley}: |N| = 2 ≥ 1 ✓  
A = {Ping, Ruiz}: |N| = /- ? -/ ≥ 2 ?
A = {4명 전체}: |N| = /- ? -/ ≥ 4 ?
결론: 완전 매칭이 /- 존재한다/존재하지 않는다 -/
```

<details>
<summary>💡 답 보기</summary>

```
A = {Ping, Ruiz}: N = {HW, NW, 무선} → |N| = 3 ≥ 2 ✓
A = {4명 전체}: N = {HW, SW, NW, 무선} → |N| = 4 ≥ 4 ✓
(모든 부분집합 검증 생략 — 모두 만족)
결론: 완전 매칭이 존재한다!

가능한 배정: Ping→무선, Quiggley→SW, Ruiz→NW, Sitea→HW
```
</details>

---

## 7. 연습 문제 — 레벨 2: Skeleton 채우기

### 연습 7.1: 이분 그래프의 같은 편 비인접 증명

```lean
-- 이분 그래프에서 같은 편 꼭지점은 인접하지 않음
theorem bipartite_no_same_side
  (adj : Fin n → Fin n → Bool)
  (side : Fin n → Bool)
  (h_bip : ∀ i j, adj i j = true → side i ≠ side j)
  (i j : Fin n) (h_same : side i = side j) :
  adj i j = false := by
  -- 힌트: h_bip의 대우를 사용
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem bipartite_no_same_side ... := by
  by_contra h
  push_neg at h
  have := h_bip i j (by cases adj i j <;> simp_all)
  exact absurd h_same this
```
</details>

### 연습 7.2: 그래프 합집합의 대칭성

```lean
theorem union_sym
  (adj1 adj2 : Fin n → Fin n → Bool)
  (h1 : ∀ i j, adj1 i j = adj1 j i)
  (h2 : ∀ i j, adj2 i j = adj2 j i) :
  ∀ i j, graphUnion adj1 adj2 i j = graphUnion adj1 adj2 j i := by
  -- 힌트: graphUnion을 전개하고 h1, h2를 적용
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem union_sym ... := by
  intro i j; simp [graphUnion]; rw [h1 i j, h2 i j]
```
</details>

### 연습 7.3: 부분그래프 차수 상한

```lean
-- 부분그래프에서 차수 ≤ 원래 그래프 차수
theorem subgraph_degree_le
  (adj sub_adj : Fin n → Fin n → Bool)
  (h : ∀ i j, sub_adj i j = true → adj i j = true)
  (v : Fin n) :
  (Finset.univ.filter fun u => sub_adj v u).card
  ≤ (Finset.univ.filter fun u => adj v u).card := by
  -- 힌트: Finset.card_le_card + Finset.filter_subset_filter
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- {u | sub_adj v u} ⊆ {u | adj v u} (h에 의해)
-- Finset.card_le_card를 적용
```
</details>

---

## 8. 연습 문제 — 레벨 3: sorry 채우기

### 연습 8.1: Qₙ이 이분임을 증명

```lean
-- n-큐브 Qₙ은 이분 그래프이다
-- 분할: V₁ = {1의 개수가 짝수}, V₂ = {1의 개수가 홀수}
-- 인접한 두 비트 스트링은 1비트 차이 → 1의 개수 홀짝 반전

-- 보조 정리: 해밍 거리 1이면 popcount의 홀짝이 다르다
theorem hamming1_flips_parity (n : ℕ) (a b : Fin n → Bool)
  (h : hammingDist a b = 1) :
  Even ((Finset.univ.filter fun i => a i).card)
  ↔ ¬ Even ((Finset.univ.filter fun i => b i).card) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 핵심: a와 b가 정확히 1비트 다르므로
-- popcount 차이 = ±1
-- 짝수 ± 1 = 홀수, 홀수 ± 1 = 짝수
```
</details>

### 연습 8.2: 모서리 제거 후 차수 변화

```lean
-- 모서리 제거 시 해당 꼭지점의 차수가 1 감소
theorem remove_edge_degree_dec
  (adj : Fin n → Fin n → Bool)
  (u v : Fin n) (h_neq : u ≠ v)
  (h_adj : adj u v = true)
  (h_sym : ∀ i j, adj i j = adj j i) :
  (Finset.univ.filter fun w => removeEdge adj u v u w).card
  = (Finset.univ.filter fun w => adj u w).card - 1 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- removeEdge 후 u의 이웃에서 v만 빠짐
-- 나머지 이웃은 동일
-- card = card - 1
```
</details>

### 연습 8.3: 완전 이분 그래프의 악수 정리

```lean
-- K_{m,n}에서 악수 정리 확인
-- Σ deg = m×n + n×m = 2mn = 2×(모서리 수)
example (m n : ℕ) : m * n + n * m = 2 * (m * n) := by
  sorry  -- ring으로 해결!
```

<details>
<summary>💡 답 보기</summary>

```lean
example (m n : ℕ) : m * n + n * m = 2 * (m * n) := by ring
```
</details>

---

## 9. 핵심 요약

1. **이분 그래프**: 꼭지점을 두 그룹으로 나눠 모서리가 그룹 간만 연결. `side : V → Bool`로 표현.
2. **정리 4**: 이분 ↔ 2-색칠 가능 ↔ 홀수 사이클 없음.
3. **완전 이분 그래프** K_{m,n}: 모서리 수 = m×n. K_{1,n} = 성형.
4. **매칭**: 겹치지 않는 모서리 집합. **완전 매칭**: V₁ 전체가 매칭.
5. **홀의 결혼이론**: 완전 매칭 존재 ↔ ∀ A ⊆ V₁, |N(A)| ≥ |A|.
6. **네트워크 위상**: 성형(K_{1,n}), 환형(Cₙ), 혼합형(Wₙ), 하이퍼큐브(Qₙ).
7. **부분그래프**: W ⊆ V, F ⊆ E. **유도된 부분그래프**: 꼭지점 → 모서리 자동.
8. **그래프 연산**: 모서리 제거/추가/축약, 꼭지점 제거, 합집합.
9. **Qₙ은 항상 이분**: popcount 홀짝으로 분류.

---

> **다음 파트 예고**: Part 13-E에서는 **그래프의 표현과 동형**(Section 10.3)을 다룬다. 인접행렬, 인접리스트, 그래프 동형의 정의와 판정을 배운다!
