# Lean4 완전 정복 가이드 — 제7-G편

## **중국인의 나머지 정리**(Chinese Remainder Theorem)와 **큰 정수의 연산**(Large Integer Arithmetic) 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 4.4절 합동 풀기 (4.4.3 중국인의 나머지 정리, 4.4.4 큰 정수의 컴퓨터 연산)  
> **선수 학습**: 제7-F편(선형합동, 역모듈로)  
> **참고**: 『Mathematics in Lean』 Chapter 9.2 (Rings — Chinese Remainder Theorem)

---

## 7G.0 이 장의 목표

1. **중국인의 나머지 정리**(CRT)가 무엇인지 이해한다
2. CRT를 이용하여 **연립 합동 시스템**을 풀 수 있다
3. **역대입법**(back substitution)으로 같은 문제를 다른 방법으로 풀 수 있다
4. **큰 정수의 연산**을 나머지 표현으로 효율적으로 수행하는 방법을 안다
5. 이 모든 것을 **Lean4 코드**로 구현한다

> 💡 **역사적 배경**: 1세기 중국의 수학자 손자(Sun-Tzu)가 다음과 같은 질문을 했다: "어떤 미지수가 있다. 3으로 나누면 2가 남고, 5로 나누면 3이 남고, 7로 나누면 2가 남는다. 이 수는 무엇일까?" 이 유명한 퍼즐이 중국인의 나머지 정리의 기원이다!

---

## 7G.1 **손자의 퍼즐**(Sun-Tzu's Puzzle) — 교재 예제 4

### 7G.1.1 문제 설정

다음 연립 합동 시스템을 풀어라:

$$x \equiv 2 \pmod{3}$$
$$x \equiv 3 \pmod{5}$$
$$x \equiv 2 \pmod{7}$$

이것은 "3으로 나누면 2가 남고, 5로 나누면 3이 남고, 7로 나누면 2가 남는 수를 찾아라"는 뜻이다.

### 7G.1.2 무작정 해보기

$x = 0, 1, 2, \ldots$을 하나씩 넣어보자:

```lean
-- 무차별 검색으로 찾기
def solveBrute (conds : List (Nat × Nat)) (bound : Nat) : List Nat :=
  (List.range bound).filter fun x =>
    conds.all fun (r, m) => x % m == r

-- 손자의 퍼즐: x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7)
#eval solveBrute [(2, 3), (3, 5), (2, 7)] 200
-- 결과: [23, 128, ...] — 23이 최소 양의 해!
```

검증해 보자:
- $23 = 7 \times 3 + 2$ → $23 \div 3$ 나머지 2 ✓
- $23 = 4 \times 5 + 3$ → $23 \div 5$ 나머지 3 ✓
- $23 = 3 \times 7 + 2$ → $23 \div 7$ 나머지 2 ✓

```lean
example : 23 % 3 = 2 := by native_decide
example : 23 % 5 = 3 := by native_decide
example : 23 % 7 = 2 := by native_decide
```

해는 23 하나만이 아니다. $23 + 105 = 128$, $23 + 210 = 233$ 등도 해이다. 왜 105인가? $3 \times 5 \times 7 = 105$이기 때문이다! 즉, 해는 $x \equiv 23 \pmod{105}$이다.

---

## 7G.2 **중국인의 나머지 정리**(Chinese Remainder Theorem) — 정리 2

### 7G.2.1 정리의 진술

> **정리 2** (중국인의 나머지 정리): $m_1, m_2, \ldots, m_n$이 **쌍으로 서로소**(pairwise coprime)인 양의 정수이고, $a_1, a_2, \ldots, a_n$이 임의의 정수라 하자. 시스템
> $$x \equiv a_1 \pmod{m_1}$$
> $$x \equiv a_2 \pmod{m_2}$$
> $$\vdots$$
> $$x \equiv a_n \pmod{m_n}$$
> 은 모듈로 $m = m_1 m_2 \cdots m_n$에서 **유일한 해**를 갖는다. (즉, $0 \le x < m$인 해 $x$가 있고 모든 다른 해는 이 해에 모듈로 $m$ 합동이다.)

### 7G.2.2 "쌍으로 서로소"란?

$m_1, m_2, \ldots, m_n$이 **쌍으로 서로소**(pairwise coprime)라 함은, 서로 다른 어떤 두 수를 골라도 $\gcd(m_i, m_j) = 1$이라는 뜻이다.

예: $\{3, 5, 7\}$은 쌍으로 서로소이다:
- $\gcd(3, 5) = 1$ ✓
- $\gcd(3, 7) = 1$ ✓  
- $\gcd(5, 7) = 1$ ✓

예: $\{3, 6, 7\}$은 쌍으로 서로소가 **아니다**:
- $\gcd(3, 6) = 3 \neq 1$ ✗

```lean
-- Lean4로 쌍으로 서로소 확인
#eval Nat.Coprime 3 5  -- true
#eval Nat.Coprime 3 7  -- true
#eval Nat.Coprime 5 7  -- true
-- {3, 5, 7}은 쌍으로 서로소 ✓

#eval Nat.Coprime 3 6  -- false
-- {3, 6, 7}은 쌍으로 서로소가 아님 ✗
```

### 7G.2.3 정리의 핵심: 왜 유일한 해가 존재하는가?

증명의 핵심 아이디어를 직관적으로 설명한다.

$m = m_1 \times m_2 \times \cdots \times m_n$이라 하자. $k = 1, 2, \ldots, n$에 대해:

1. $M_k = m / m_k$ (즉, $m_k$만 제외한 나머지의 곱)를 정의한다
2. $m_i$와 $M_k$의 관계: $i \neq k$이면 $m_i | M_k$이고, $\gcd(m_k, M_k) = 1$이다
3. $\gcd(m_k, M_k) = 1$이므로 $M_k$의 역모듈로 $y_k$가 존재한다: $M_k y_k \equiv 1 \pmod{m_k}$
4. 해를 구성한다: $x = a_1 M_1 y_1 + a_2 M_2 y_2 + \cdots + a_n M_n y_n$

이 $x$가 모든 합동을 만족하는 이유:
- $x \pmod{m_k}$를 계산하면, $j \neq k$일 때 $M_j \equiv 0 \pmod{m_k}$이므로 $a_j M_j y_j$ 항들은 모두 0
- 남는 것은 $a_k M_k y_k \equiv a_k \cdot 1 = a_k \pmod{m_k}$

---

## 7G.3 교재 예제 5: CRT 풀이 (상세 과정)

### 7G.3.1 문제

손자의 퍼즐을 CRT 공식으로 풀어보자.

$x \equiv 2 \pmod{3}$, $x \equiv 3 \pmod{5}$, $x \equiv 2 \pmod{7}$

### 7G.3.2 풀이

**1단계**: $m = 3 \times 5 \times 7 = 105$

**2단계**: $M_k = m / m_k$를 계산
- $M_1 = 105 / 3 = 35$
- $M_2 = 105 / 5 = 21$
- $M_3 = 105 / 7 = 15$

**3단계**: $M_k y_k \equiv 1 \pmod{m_k}$인 $y_k$를 구한다
- $35 y_1 \equiv 1 \pmod{3}$: $35 \equiv 2 \pmod{3}$이고 $2 \times 2 = 4 \equiv 1 \pmod{3}$이므로 $y_1 = 2$
- $21 y_2 \equiv 1 \pmod{5}$: $21 \equiv 1 \pmod{5}$이므로 $y_2 = 1$
- $15 y_3 \equiv 1 \pmod{7}$: $15 \equiv 1 \pmod{7}$이므로 $y_3 = 1$

**4단계**: 해를 합성

$$x \equiv a_1 M_1 y_1 + a_2 M_2 y_2 + a_3 M_3 y_3$$
$$= 2 \times 35 \times 2 + 3 \times 21 \times 1 + 2 \times 15 \times 1$$
$$= 140 + 63 + 30 = 233$$
$$\equiv 23 \pmod{105}$$

```lean
-- 각 단계를 Lean4로 검증
-- M_k 계산
#eval 105 / 3   -- 35 = M₁
#eval 105 / 5   -- 21 = M₂
#eval 105 / 7   -- 15 = M₃

-- y_k 계산 (역모듈로)
example : (35 * 2) % 3 = 1 := by native_decide  -- y₁ = 2
example : (21 * 1) % 5 = 1 := by native_decide  -- y₂ = 1
example : (15 * 1) % 7 = 1 := by native_decide  -- y₃ = 1

-- 해 합성
#eval (2 * 35 * 2 + 3 * 21 * 1 + 2 * 15 * 1) % 105  -- 23

-- 최종 검증
example : 23 % 3 = 2 := by native_decide
example : 23 % 5 = 3 := by native_decide
example : 23 % 7 = 2 := by native_decide
```

### 7G.3.3 CRT 함수 구현

```lean
-- 확장 유클리드 알고리즘 (7-F편에서 재사용)
def extGcd : Int → Int → (Int × Int × Int)
  | a, 0 => (a, 1, 0)
  | a, b =>
    let (g, s, t) := extGcd b (a % b)
    (g, t, s - (a / b) * t)

-- 중국인의 나머지 정리 풀이기
-- 입력: (나머지, 모듈러스) 쌍의 리스트
-- 출력: (해, 전체 모듈러스)
def solveCRT (conds : List (Nat × Nat)) : Option (Nat × Nat) :=
  let m := conds.foldl (fun acc (_, mi) => acc * mi) 1
  let terms := conds.map fun (ai, mi) =>
    let bigM := m / mi
    let (_, yi, _) := extGcd (Int.ofNat bigM) (Int.ofNat mi)
    let yiNat := ((yi % Int.ofNat mi + Int.ofNat mi) % Int.ofNat mi).toNat
    ai * bigM * yiNat
  let x := terms.foldl (· + ·) 0 % m
  some (x, m)

#eval solveCRT [(2, 3), (3, 5), (2, 7)]  -- some (23, 105)
```

---

## 7G.4 **역대입법**(Back Substitution) — 교재 예제 6

### 7G.4.1 역대입법이란?

CRT의 공식은 계산이 복잡할 수 있다. **역대입법**(back substitution)은 합동을 하나씩 풀면서 대입해 나가는 더 직관적인 방법이다.

### 7G.4.2 교재 예제 6

$x \equiv 1 \pmod{5}$, $x \equiv 2 \pmod{6}$, $x \equiv 3 \pmod{7}$을 풀어라.

**풀이**:

**1단계**: 첫 번째 합동 $x \equiv 1 \pmod{5}$에서 $x = 5t + 1$ (정리 4.1절)

**2단계**: 두 번째 합동에 대입: $5t + 1 \equiv 2 \pmod{6}$

$5t \equiv 1 \pmod{6}$

이것을 풀면 $t \equiv 5 \pmod{6}$ (왜? $5 \times 5 = 25 \equiv 1 \pmod{6}$)

따라서 $t = 6u + 5$이고, $x = 5(6u + 5) + 1 = 30u + 26$

**3단계**: 세 번째 합동에 대입: $30u + 26 \equiv 3 \pmod{7}$

$30u \equiv -23 \equiv -23 + 28 = 5 \pmod{7}$

$2u \equiv 5 \pmod{7}$ (왜? $30 \equiv 2 \pmod{7}$)

이것을 풀면 $u \equiv 6 \pmod{7}$ (왜? $2 \times 6 = 12 \equiv 5 \pmod{7}$)

따라서 $u = 7v + 6$이고, $x = 30(7v + 6) + 26 = 210v + 206$

**결론**: $x \equiv 206 \pmod{210}$

```lean
-- 각 단계 검증
example : (5 * 5) % 6 = 1 := by native_decide  -- t ≡ 5 (mod 6)
example : (30 * 6 + 26) % 7 = 3 := by native_decide  -- 206 % 7 = 3
example : 206 % 5 = 1 := by native_decide
example : 206 % 6 = 2 := by native_decide
example : 206 % 7 = 3 := by native_decide

-- 3 × 5 × 7 = 210 = 전체 모듈러스
#eval 5 * 6 * 7  -- 210
```

### 7G.4.3 역대입법 함수

```lean
-- 역대입법 구현
def solveBackSub : List (Nat × Nat) → Option (Nat × Nat)
  | [] => some (0, 1)
  | [(a, m)] => some (a % m, m)
  | (a1, m1) :: rest =>
    match solveBackSub rest with
    | none => none
    | some (partX, partM) =>
      -- partX ≡ 나머지 합동들의 해 (mod partM)
      -- 추가로 x ≡ a1 (mod m1)을 만족해야 함
      -- x = partM * t + partX로 놓고 (partM * t + partX) ≡ a1 (mod m1) 풀기
      let target := ((Int.ofNat a1 - Int.ofNat partX) % Int.ofNat m1 + Int.ofNat m1) % Int.ofNat m1
      let (g, inv, _) := extGcd (Int.ofNat partM) (Int.ofNat m1)
      if g.toNat != 1 then none
      else
        let t := (target * inv % Int.ofNat m1 + Int.ofNat m1) % Int.ofNat m1
        let newM := partM * m1
        let x := (partM * t.toNat + partX) % newM
        some (x, newM)

#eval solveBackSub [(1, 5), (2, 6), (3, 7)]  -- some (206, 210)
```

---

## 7G.5 연습문제 세트 1: CRT 기초

### 연습 1-1: 교재 연습문제 20

중국인의 나머지 정리의 증명에서 사용된 해법을 이용하여 다음 합동 시스템의 모든 해를 구하라.

$x \equiv 2 \pmod{3}$, $x \equiv 1 \pmod{4}$, $x \equiv 3 \pmod{5}$

```lean
#eval solveCRT [(2, 3), (1, 4), (3, 5)]  -- (?, 60)

-- 검증
example : sorry % 3 = 2 := by native_decide
example : sorry % 4 = 1 := by native_decide
example : sorry % 5 = 3 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval solveCRT [(2, 3), (1, 4), (3, 5)]  -- some (53, 60)

example : 53 % 3 = 2 := by native_decide
example : 53 % 4 = 1 := by native_decide
example : 53 % 5 = 3 := by native_decide
```

**풀이**: $m = 60$, $M_1 = 20$, $M_2 = 15$, $M_3 = 12$.
- $20 y_1 \equiv 1 \pmod{3}$: $y_1 = 2$ ($20 \cdot 2 = 40 \equiv 1$)
- $15 y_2 \equiv 1 \pmod{4}$: $y_2 = 3$ ($15 \cdot 3 = 45 \equiv 1$)
- $12 y_3 \equiv 1 \pmod{5}$: $y_3 = 3$ ($12 \cdot 3 = 36 \equiv 1$)

$x = 2 \cdot 20 \cdot 2 + 1 \cdot 15 \cdot 3 + 3 \cdot 12 \cdot 3 = 80 + 45 + 108 = 233 \equiv 53 \pmod{60}$

</details>

### 연습 1-2: 교재 연습문제 21

$x \equiv 1 \pmod{2}$, $x \equiv 2 \pmod{3}$, $x \equiv 3 \pmod{5}$, $x \equiv 4 \pmod{11}$

```lean
#eval solveCRT [(1, 2), (2, 3), (3, 5), (4, 11)]

example : sorry % 2 = 1 := by native_decide
example : sorry % 3 = 2 := by native_decide
example : sorry % 5 = 3 := by native_decide
example : sorry % 11 = 4 := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval solveCRT [(1, 2), (2, 3), (3, 5), (4, 11)]
-- some ((?), 330)  -- 직접 확인해보자!

-- 무차별 검색으로 확인
#eval solveBrute [(1, 2), (2, 3), (3, 5), (4, 11)] 330
```

</details>

### 연습 1-3: 교재 연습문제 22 — 역대입법

역대입법을 사용하여 합동 시스템 $x \equiv 3 \pmod{6}$, $x \equiv 4 \pmod{7}$을 풀어라.

```lean
-- 1단계: x = 6t + 3
-- 2단계: 6t + 3 ≡ 4 (mod 7) → 6t ≡ 1 (mod 7)
-- 6의 역(mod 7) = 6 (왜? 6*6=36≡1 mod 7)
-- t ≡ 6 (mod 7)
-- x = 6(7v + 6) + 3 = 42v + 39
-- x ≡ 39 (mod 42)

example : 39 % 6 = sorry := by native_decide
example : 39 % 7 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 39 % 6 = 3 := by native_decide
example : 39 % 7 = 4 := by native_decide
-- x ≡ 39 (mod 42) ✓

-- 검증: 6 * 6 mod 7 = 36 mod 7 = 1 ✓
example : (6 * 6) % 7 = 1 := by native_decide
```

</details>

---

## 7G.6 **큰 정수의 컴퓨터 연산**(Computer Arithmetic with Large Integers) — 4.4.4절

### 7G.6.1 핵심 아이디어

매우 큰 정수(예: 수백 자리)의 덧셈과 곱셈은 직접 계산하면 느리다. 중국인의 나머지 정리를 이용하면 **작은 수들의 연산**으로 대체할 수 있다!

**방법**:
1. 쌍으로 서로소인 작은 수들 $m_1, m_2, \ldots, m_n$을 선택한다
2. 큰 수 $a$를 $(a \bmod m_1, a \bmod m_2, \ldots, a \bmod m_n)$으로 표현한다
3. 각 성분별로 **독립적으로** 연산한다 (병렬 처리 가능!)
4. CRT를 써서 결과를 복원한다

### 7G.6.2 교재 예제 7: 12 이하의 수를 (mod 3, mod 4)로 표현

$m_1 = 3$, $m_2 = 4$이고 $m = 3 \times 4 = 12$이다.

| 수 | (mod 3, mod 4) |
|---|---|
| 0 | (0, 0) |
| 1 | (1, 1) |
| 2 | (2, 2) |
| 3 | (0, 3) |
| 4 | (1, 0) |
| 5 | (2, 1) |
| 6 | (0, 2) |
| 7 | (1, 3) |
| 8 | (2, 0) |
| 9 | (0, 1) |
| 10 | (1, 2) |
| 11 | (2, 3) |

```lean
-- Lean4로 표현
def toModPair (n : Nat) : Nat × Nat := (n % 3, n % 4)

#eval (List.range 12).map toModPair
-- [(0,0), (1,1), (2,2), (0,3), (1,0), (2,1), (0,2), (1,3), (2,0), (0,1), (1,2), (2,3)]
```

### 7G.6.3 교재 예제 8: 큰 수의 덧셈

$m_1 = 99$, $m_2 = 98$, $m_3 = 97$, $m_4 = 95$ (쌍으로 서로소)

$m = 99 \times 98 \times 97 \times 95 = 89{,}403{,}930$

$123{,}684$를 나머지로 표현:

```lean
-- 123684의 나머지 표현
#eval 123684 % 99  -- 33
#eval 123684 % 98  -- 8
#eval 123684 % 97  -- 9
#eval 123684 % 95  -- 89
-- 123684 ↔ (33, 8, 9, 89)
```

$413{,}456$를 나머지로 표현:

```lean
#eval 413456 % 99  -- 32
#eval 413456 % 98  -- 92
#eval 413456 % 97  -- 42
#eval 413456 % 95  -- 16
-- 413456 ↔ (32, 92, 42, 16)
```

**덧셈**: 성분별로 더하고 나머지를 취한다:

$$(\mathbf{33}, 8, 9, 89) + (32, 92, 42, 16) = (65 \bmod 99, 100 \bmod 98, 51 \bmod 97, 105 \bmod 95)$$
$$= (65, 2, 51, 10)$$

```lean
-- 성분별 덧셈
#eval (33 + 32) % 99  -- 65
#eval (8 + 92) % 98   -- 2
#eval (9 + 42) % 97   -- 51
#eval (89 + 16) % 95  -- 10

-- 실제 합: 123684 + 413456 = 537140
#eval 123684 + 413456  -- 537140

-- CRT로 복원: (65, 2, 51, 10)에서 537140을 복원
#eval 537140 % 99  -- 65 ✓
#eval 537140 % 98  -- 2  ✓
#eval 537140 % 97  -- 51 ✓
#eval 537140 % 95  -- 10 ✓
```

> 💡 핵심 장점: 100보다 작은 수의 연산만으로 큰 수의 연산을 수행했다! 네 개의 작은 연산은 **병렬로** 수행할 수 있으므로 속도가 빨라진다.

### 7G.6.4 $2^k - 1$ 형태의 좋은 나누는 수

교재에서는 나누는 수로 $2^k - 1$ 형태의 수를 추천한다. 이유:
- 이진 모듈로 연산이 쉽다
- 쌍으로 서로소인 수를 찾기 쉽다 (예: $\gcd(2^a - 1, 2^b - 1) = 2^{\gcd(a,b)} - 1$)

```lean
-- 2^k - 1 형태의 수들
#eval (2^35 - 1 : Nat)  -- 34359738367
-- 2^35보다 작은 수들의 연산이 가능!

-- 쌍으로 서로소 확인
#eval Nat.gcd (2^35 - 1) (2^34 - 1)  -- 2^gcd(35,34) - 1 = 2^1 - 1 = 1 ✓
```

---

## 7G.7 연습문제 세트 2: CRT 심화

### 연습 2-1: 교재 연습문제 26

다음 합동 시스템의 해가 존재한다면 모두 구하라.

$x \equiv 5 \pmod{6}$, $x \equiv 3 \pmod{10}$, $x \equiv 8 \pmod{15}$

```lean
-- 먼저 쌍으로 서로소인지 확인!
#eval Nat.gcd 6 10   -- ?
#eval Nat.gcd 6 15   -- ?
#eval Nat.gcd 10 15  -- ?
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval Nat.gcd 6 10   -- 2 ≠ 1!
#eval Nat.gcd 6 15   -- 3 ≠ 1!
#eval Nat.gcd 10 15  -- 5 ≠ 1!
```

쌍으로 서로소가 **아니므로** CRT를 직접 적용할 수 없다! 

그러나 해가 존재할 수도 있다. 무차별 검색으로 확인:

```lean
#eval solveBrute [(5, 6), (3, 10), (8, 15)] 500
-- 결과가 비어 있으면 해가 없고, 있으면 해가 있다
```

해가 존재하려면 합동 조건들이 호환되어야 한다. $x \equiv 5 \pmod{6}$은 $x$가 홀수를, $x \equiv 3 \pmod{10}$은 $x$가 홀수를 의미하므로 양립 가능하다. 그러나 모든 조건을 동시에 만족하는 $x$가 실제로 있는지는 검사해 봐야 한다.

</details>

### 연습 2-2: 교재 연습문제 31-32

2로 나누면 1이 남고 3으로 나누면 1이 남는 정수는 무엇인가?

```lean
-- x ≡ 1 (mod 2), x ≡ 1 (mod 3)
-- gcd(2,3) = 1 ✓
#eval solveCRT [(1, 2), (1, 3)]  -- some (?, 6)
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval solveCRT [(1, 2), (1, 3)]  -- some (1, 6)
-- x ≡ 1 (mod 6)
-- 즉 x = 1, 7, 13, 19, ...
```

</details>

### 연습 2-3: 성분별 연산 연습

$a = 50$과 $b = 75$를 $(a \bmod 3, a \bmod 4)$와 $(b \bmod 3, b \bmod 4)$로 표현한 뒤, $a + b$를 나머지 연산으로 구하시오.

```lean
-- a = 50의 나머지 표현
#eval (50 % 3, 50 % 4)  -- (?, ?)

-- b = 75의 나머지 표현
#eval (75 % 3, 75 % 4)  -- (?, ?)

-- 성분별 덧셈 (mod 3, mod 4)
-- (50%3 + 75%3) % 3 = ?
-- (50%4 + 75%4) % 4 = ?

-- 실제 합
#eval 50 + 75  -- 125
-- 125의 나머지 표현과 일치하는지 확인
#eval (125 % 3, 125 % 4)
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (50 % 3, 50 % 4)   -- (2, 2)
#eval (75 % 3, 75 % 4)   -- (0, 3)

-- 성분별 덧셈
#eval (2 + 0) % 3  -- 2
#eval (2 + 3) % 4  -- 1
-- 결과: (2, 1)

-- 125의 나머지 표현
#eval (125 % 3, 125 % 4)  -- (2, 1) ✓ 일치!
```

</details>

---

## 7G.8 **Lean4 Mathlib의 CRT** (심화)

### 7G.8.1 ZMod 타입

Lean4의 Mathlib 라이브러리에는 $\mathbb{Z}/n\mathbb{Z}$를 나타내는 `ZMod n` 타입이 있다. 중국인의 나머지 정리는 이 타입을 이용하여 다음과 같이 표현된다:

```lean
-- Mathematics in Lean에서 발췌
-- 쌍으로 서로소인 a : ι → ℕ에 대해
-- ZMod (∏ i, a i) ≃+* ∏ i, ZMod (a i)
-- 즉, Z/(m₁m₂...mₙ)Z ≅ Z/m₁Z × Z/m₂Z × ... × Z/mₙZ (환 동형사상)
```

이것은 CRT의 가장 우아한 형태이다. 나머지로 표현하는 것이 **대수적 구조**(곱셈과 덧셈)를 보존한다는 것을 말하고 있다!

### 7G.8.2 Mathlib에서의 CRT

```lean
-- Mathlib에서 ZMod의 CRT를 사용하는 예
-- (고급: 이해하지 못해도 괜찮다!)
-- import Mathlib.Data.ZMod.Basic
-- example : ZMod (3 * 5 * 7) ≃+* ZMod 3 × ZMod 5 × ZMod 7 := ...
```

> 💡 이 수준의 형식화는 대학원 수학과에서나 볼 수 있는 것이다. 지금은 "CRT가 Mathlib에도 있구나" 정도만 알면 된다!

---

## 7G.9 전술 요약

| 전술 | 용도 | 예시 |
|------|------|------|
| `native_decide` | 구체적 숫자 계산 | `23 % 3 = 2` |
| `norm_num` | 정수 산술 | 큰 수의 계산 |
| `use` | 존재 증인 | `use 23` |
| `decide` | 유한 범위 전수 검사 | `∀ x : Fin n, ...` |
| `ring` | 대수적 등식 | 다항식 정리 |

---

## 7G.10 핵심 정리 요약

| 이름 | 내용 |
|------|------|
| **정리 2** (CRT) | $m_i$가 쌍으로 서로소이면 연립 합동이 유일한 해를 가진다 (mod $m_1 \cdots m_n$) |
| **CRT 풀이법** | $x = \sum a_k M_k y_k$, 여기서 $M_k = m/m_k$, $M_k y_k \equiv 1 \pmod{m_k}$ |
| **역대입법** | 합동을 하나씩 풀면서 대입해 나간다 |
| **나머지 표현** | $(a \bmod m_1, \ldots, a \bmod m_n)$으로 큰 수를 표현하면 성분별 연산 가능 |

---

## 다음 편(7-H) 예고

**제7-H편** (페르마의 작은 정리)에서는:
- **페르마의 작은 정리**(Fermat's Little Theorem): $a^{p-1} \equiv 1 \pmod{p}$
- **의사소수**(pseudoprime)와 **카마이클 수**(Carmichael number)
- **기본 루트**(primitive root)와 **이산 로그**(discrete logarithm)

를 다룬다.

---

**(끝)**
