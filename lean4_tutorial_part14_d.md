# Part 14-D: 회로의 최소화 — 카르노맵과 퀸-맥클러스키 방법

> **Rosen 이산수학 8판 · Section 12.4 기반**
> **『Mathematics in Lean』 + Lean 4 공식화**

---

## 0. 들어가며: 이 파트에서 배울 것

Part 14-C에서는 부울 식을 논리 게이트 회로로 구현하는 방법을 배웠다. 그런데 곱의 합 표준형으로 얻은 부울 식은 필요한 것보다 **더 많은 항**(term)을 가지는 경우가 대부분이다. 게이트가 많으면 비용이 올라가고, 공간을 차지하며, 전력 소모와 발열이 증가한다.

이 파트에서는 부울 식을 **더 간단하게** 만드는, 즉 회로를 **최소화**(minimization)하는 방법을 배운다.

이 파트에서 다루는 내용:

1. **회로 최소화**의 필요성 — 왜 간단한 회로가 좋은가?
2. **카르노맵**(Karnaugh map) — 2, 3, 4변수 부울 식의 시각적 간소화
3. **임플리컨트**(implicant), **프라임 임플리컨트**(prime implicant), **에센셜 프라임 임플리컨트**(essential prime implicant)
4. **무정의 조건**(Don't Care condition) — 사용 안 하는 입력 활용
5. **퀸-맥클러스키**(Quine-McCluskey) 방법 — 컴퓨터로 자동화 가능한 최소화
6. Lean 4로 최소화 전후의 동치성 검증

---

## 1. 왜 최소화가 필요한가?

### 1.1 동일 기능, 다른 복잡도

같은 부울 함수도 여러 부울 식으로 표현할 수 있다. 식이 다르면 필요한 게이트 수도 다르다.

**예**: $x = y = z = 1$ 또는 $x = z = 1, y = 0$일 때 1을 출력하는 회로

- **곱의 합 표준형**: $xyz + x\overline{y}z$ → AND 2개 + OR 1개 + 인버터 1개 = **4개 게이트**
- **간소화**: $xyz + x\overline{y}z = (y + \overline{y}) \cdot xz = 1 \cdot xz = xz$ → AND 1개 = **1개 게이트!**

> 🏭 **비유**: 같은 요리를 만드는데, 한 레시피는 도구 4개를 쓰고 다른 레시피는 1개만 쓴다면, 당연히 1개짜리가 효율적이다.

```lean
-- 원래 식
def f_original (x y z : Bool) : Bool := (x && y && z) || (x && !y && z)

-- 간소화된 식
def f_simplified (x y z : Bool) : Bool := x && z

-- 동치 검증
example : ∀ x y z : Bool, f_original x y z = f_simplified x y z := by decide
```

### 1.2 간소화의 핵심 원리

두 최소항이 **단 하나의 변수만** 다르면, 그 변수를 제거할 수 있다:

$$xy\overline{z} + xyz = x(y\overline{z} + yz) = x \cdot y \cdot (\overline{z} + z) = xy \cdot 1 = xy$$

일반적으로: $A \cdot B + A \cdot \overline{B} = A$ (어떤 부분식 $A$에 대해)

이것이 카르노맵과 퀸-맥클러스키 방법의 **기본 원리**이다.

---

## 2. 카르노맵 — 시각적 간소화 도구

### 2.1 카르노맵이란?

**카르노맵**(Karnaugh map, K-map)은 부울 함수의 최소항들을 2차원 격자에 배치하여, **인접한 최소항**들을 눈으로 묶어 간소화하는 도구이다. 1953년 모리스 카르노(Maurice Karnaugh)가 제안하였다.

> 🗺️ **비유**: 진리표가 "숫자 목록"이라면, 카르노맵은 그 숫자들을 "지도" 위에 배치한 것이다. 지도에서 이웃한 영역을 큰 덩어리로 묶으면 간소화가 된다.

### 2.2 2변수 카르노맵

2변수 $x, y$의 카르노맵은 2×2 격자이다:

```
        y=0    y=1
x=0  │ x̄ȳ   │ x̄y  │
x=1  │ xȳ   │ xy   │
```

각 셀은 하나의 최소항에 대응한다. **인접한** 셀은 하나의 변수만 차이가 난다.

**예제 1** (Rosen):

**(a)** $xy + x\overline{y}$의 카르노맵:

```
        y=0    y=1
x=0  │  0    │  0   │
x=1  │  1    │  1   │    ← xȳ와 xy 모두 1
```

두 개의 1이 가로로 인접 → $y$를 제거 → **결과: $x$**

```lean
example : ∀ x y : Bool, (x && y) || (x && !y) = x := by decide
```

**(b)** $xy + \overline{x}\overline{y}$의 카르노맵:

```
        y=0    y=1
x=0  │  1    │  0   │    ← x̄ȳ
x=1  │  0    │  1   │    ← xy
```

두 개의 1이 대각선 → 인접하지 않음 → **더 이상 간소화 불가**: $xy + \overline{x}\overline{y}$

**(c)** $xy + \overline{x}y + x\overline{y}$의 카르노맵:

```
        y=0    y=1
x=0  │  0    │  1   │    ← x̄y
x=1  │  1    │  1   │    ← xȳ, xy
```

묶기: 오른쪽 열(x̄y + xy = y) + 아래 행(xȳ + xy = x) → 하지만 xy가 중복 사용된다. 가장 큰 묶음으로:
- 오른쪽 열 전체: $y$
- 아래 행 전체: $x$
- **결과: $x + y$**

```lean
example : ∀ x y : Bool,
  (x && y) || (!x && y) || (x && !y) = x || y := by decide
```

### 2.3 3변수 카르노맵

3변수 $x, y, z$의 카르노맵은 2×4 격자이다. 열의 배열이 특별하다 — **그레이 코드**(Gray code) 순서를 따른다:

```
         yz=00  yz=01  yz=11  yz=10
x=0    │ x̄ȳz̄  │ x̄ȳz  │ x̄yz  │ x̄yz̄  │
x=1    │ xȳz̄  │ xȳz  │ xyz  │ xyz̄  │
```

> ⚠️ **핵심**: 열 순서가 00, 01, **11**, **10**이다! 00→01→10→11이 **아니다**! 그레이 코드에서는 인접한 코드가 **1비트만 차이**난다. 이래야 카르노맵에서 인접한 셀이 정확히 1변수만 다른 최소항이 된다.

또한 **첫 번째 열과 마지막 열은 서로 인접**한 것으로 간주한다 (원통형으로 말린 것처럼).

#### 블록 크기와 간소화

| 블록 크기 | 제거되는 변수 수 | 남는 변수 수 |
|----------|---------------|------------|
| 1셀 | 0 | 3 (최소항 그대로) |
| 2셀 | 1 | 2 |
| 4셀 | 2 | 1 |
| 8셀 (전체) | 3 | 0 (항상 1) |

**예제 3** (Rosen):

**(a)** $xyz + x\overline{y}z + \overline{x}yz + \overline{x}\overline{y}z + \overline{x}\overline{y}\overline{z}$

카르노맵에 1을 채우고 묶으면:

```
         yz=00  yz=01  yz=11  yz=10
x=0    │  1    │  1    │  1    │  0   │
x=1    │  0    │  1    │  1    │  0   │
```

묶음:
- yz=01 열 전체(2셀): $\overline{y}z$ (x가 제거됨)
- yz=11 열 전체(2셀): $yz$ (x가 제거됨)
- 아, 더 크게: yz=01과 yz=11 열, x=0 행 두 셀 + x=1 행 두 셀 = 4셀 → $z$
- x=0, yz=00: 혼자 남음 → $\overline{x}\overline{y}\overline{z}$

**결과**: $z + \overline{x}\overline{y}\overline{z}$

음, 다시 정리하자. 전체 4개의 z=1인 셀(yz=01과 yz=11의 모든 행)이 하나의 4셀 블록이 되어 $z$이다. 그리고 x=0, yz=00은 단독이므로 $\overline{x}\overline{y}\overline{z}$이다.

```lean
-- 원래 식
def f_3a (x y z : Bool) : Bool :=
  (x && y && z) || (x && !y && z) || (!x && y && z) ||
  (!x && !y && z) || (!x && !y && !z)

-- 최소화된 식
def f_3a_min (x y z : Bool) : Bool := z || (!x && !y && !z)

-- 더 간소화: z || (!x && !y && !z) = z || (!x && !y)
-- 왜냐하면 z=0일 때 !x && !y && !z = !x && !y && true = !x && !y
-- z=1일 때 z=1이므로 OR의 결과는 1
-- 따라서 z || (!x && !y)
def f_3a_min2 (x y z : Bool) : Bool := z || (!x && !y)

example : ∀ x y z : Bool, f_3a x y z = f_3a_min2 x y z := by decide
```

**(b)** $\overline{x}\overline{y}z + \overline{x}yz + x\overline{y}z + xy\overline{z} + xyz$

```lean
def f_3b (x y z : Bool) : Bool :=
  (!x && !y && z) || (!x && y && z) || (x && !y && z) ||
  (x && y && !z) || (x && y && z)

-- 카르노맵으로 최소화하면: y + xz
-- y가 1인 4셀을 묶고, xz를 묶으면 된다
-- 아, 다시: xy̅z, x̅y̅z, x̅yz, xyz → z 열에서 3개, xy̅z̄ → x행에서...
-- 정확히: y + xz
def f_3b_min (x y z : Bool) : Bool := y || (x && z)

example : ∀ x y z : Bool, f_3b x y z = f_3b_min x y z := by decide
```

---

## 3. 4변수 카르노맵

4변수 $w, x, y, z$의 카르노맵은 4×4 격자이다:

```
          yz=00  yz=01  yz=11  yz=10
wx=00   │       │       │       │       │
wx=01   │       │       │       │       │
wx=11   │       │       │       │       │
wx=10   │       │       │       │       │
```

행과 열 모두 **그레이 코드** 순서(00, 01, 11, 10)이다. 첫 행과 마지막 행, 첫 열과 마지막 열은 각각 **인접**한 것으로 간주한다 (도넛 모양으로 말린 것처럼).

블록 크기:

| 블록 | 제거 변수 수 | 남는 변수 수 |
|------|-----------|------------|
| 1셀 | 0 | 4 |
| 2셀 | 1 | 3 |
| 4셀 | 2 | 2 |
| 8셀 | 3 | 1 |
| 16셀 | 4 | 0 (항상 1) |

---

## 4. 임플리컨트, 프라임 임플리컨트, 에센셜 프라임 임플리컨트

이 세 개념은 최소화의 핵심이다.

### 4.1 임플리컨트 (Implicant)

카르노맵에서 1로 채워진 셀들의 **묶음**(블록) 또는 단독 셀. 즉, 결합될 수 있는 최소항들의 모임이다.

### 4.2 프라임 임플리컨트 (Prime Implicant)

**더 큰 블록에 포함되지 않는** 임플리컨트. 즉, 더 이상 변수를 줄이기 위해 다른 항과 결합할 수 없는 상태이다.

> 🧩 **비유**: 퍼즐에서 "가능한 가장 큰 조각". 이 조각을 더 큰 조각에 합칠 수 없다.

### 4.3 에센셜 프라임 임플리컨트 (Essential Prime Implicant)

프라임 임플리컨트 중에서, **오직 이 프라임 임플리컨트만이 커버하는 1이 존재**하는 것. 다른 프라임 임플리컨트로는 대체할 수 없으므로, 최소화 결과에 **반드시 포함**되어야 한다.

> 🔑 **비유**: "이 열쇠만이 열 수 있는 문이 있다" → 이 열쇠는 반드시 필요하다.

### 4.4 최소화 절차 요약

1. 모든 **프라임 임플리컨트**를 찾는다 (가장 큰 블록들)
2. **에센셜 프라임 임플리컨트**를 찾아 반드시 포함시킨다
3. 아직 커버되지 않은 1이 있으면, 추가 프라임 임플리컨트를 선택한다
4. 선택된 프라임 임플리컨트들의 부울 합이 최소화된 결과이다

---

## 5. 무정의 조건 (Don't Care)

### 5.1 개념

어떤 입력 조합이 **절대 발생하지 않는** 경우, 그 출력은 0이든 1이든 상관없다. 이것을 **무정의 조건**(Don't Care)이라 하고 카르노맵에서 **d**로 표시한다.

d를 **1처럼** 활용하여 더 큰 블록을 만들면, 더 효율적인 최소화가 가능하다!

### 5.2 예제: BCD 코드 (Rosen 예제 8)

**BCD**(Binary Coded Decimal)는 10진수 0~9를 4비트 이진수로 표현한다. 4비트로는 0~15까지 16개를 코딩할 수 있지만, 10~15는 **사용하지 않는다**.

입력이 5 이상이면 1, 5 미만이면 0을 출력하는 회로:

| 10진수 | $w$ | $x$ | $y$ | $z$ | 출력 $F$ |
|--------|-----|-----|-----|-----|---------|
| 0 | 0 | 0 | 0 | 0 | 0 |
| 1 | 0 | 0 | 0 | 1 | 0 |
| 2 | 0 | 0 | 1 | 0 | 0 |
| 3 | 0 | 0 | 1 | 1 | 0 |
| 4 | 0 | 1 | 0 | 0 | 0 |
| 5 | 0 | 1 | 0 | 1 | **1** |
| 6 | 0 | 1 | 1 | 0 | **1** |
| 7 | 0 | 1 | 1 | 1 | **1** |
| 8 | 1 | 0 | 0 | 0 | **1** |
| 9 | 1 | 0 | 0 | 1 | **1** |
| 10-15 | — | — | — | — | **d** (Don't Care) |

무정의 조건을 활용한 최소화 결과: $F = w + xy + xz$

```lean
-- BCD 5 이상 판별 회로 (최소화 전)
def bcd_ge5_original (w x y z : Bool) : Bool :=
  -- 곱의 합 표준형: 5,6,7,8,9에 대한 최소항
  (!w && x && !y && z) || (!w && x && y && !z) ||
  (!w && x && y && z) || (w && !x && !y && !z) ||
  (w && !x && !y && z)

-- 무정의 조건 활용 최소화 후
def bcd_ge5_minimized (w x y z : Bool) : Bool :=
  w || (x && y) || (x && z)

-- BCD 유효 범위(0-9)에서 동치 검증
-- Don't Care 입력(10-15)은 출력이 달라도 상관없다!
example : ∀ w x y z : Bool,
  -- BCD 유효 범위: wxyz가 0~9
  let val := (if w then 8 else 0) + (if x then 4 else 0) +
             (if y then 2 else 0) + (if z then 1 else 0)
  val ≤ 9 →
  bcd_ge5_original w x y z = bcd_ge5_minimized w x y z := by decide
```

---

## 6. 퀸-맥클러스키 방법 — 체계적 최소화

### 6.1 왜 필요한가?

카르노맵은 사람이 눈으로 보고 묶는 방법이므로:
- 4변수까지는 쉽다
- 5~6변수는 복잡하다
- 7변수 이상은 사실상 불가능하다

**퀸-맥클러스키**(Quine-McCluskey) 방법은 **컴퓨터로 자동화**할 수 있는 체계적 최소화 알고리즘이다.

### 6.2 알고리즘 개요

**1단계**: 프라임 임플리컨트 찾기
1. 최소항을 비트열로 표현한다 (변수가 그대로이면 1, 보수이면 0)
2. 비트열의 1의 개수로 그룹을 나눈다
3. 1의 개수가 1차이 나는 그룹끼리 비교한다
4. 한 비트만 다른 쌍을 찾아 합친다 (다른 비트 자리에 '-' 표시)
5. 더 이상 합칠 수 없을 때까지 반복한다
6. 합쳐지지 않고 남은 항들이 **프라임 임플리컨트**이다

**2단계**: 에센셜 프라임 임플리컨트 선택
1. 각 프라임 임플리컨트가 커버하는 최소항을 표로 만든다
2. 한 프라임 임플리컨트만 커버하는 최소항이 있으면 → 에센셜
3. 에센셜을 선택하고, 커버된 최소항을 제거한다
4. 남은 최소항을 커버할 프라임 임플리컨트를 추가 선택한다

### 6.3 예제 9 (Rosen): $xyz + x\overline{y}z + \overline{x}yz + \overline{x}\overline{y}z + \overline{x}\overline{y}\overline{z}$

**1단계**: 비트열 표현 및 그룹화

| 최소항 | 비트열 | 1의 수 |
|--------|--------|--------|
| $xyz$ | 111 | 3 |
| $x\overline{y}z$ | 101 | 2 |
| $\overline{x}yz$ | 011 | 2 |
| $\overline{x}\overline{y}z$ | 001 | 1 |
| $\overline{x}\overline{y}\overline{z}$ | 000 | 0 |

그룹 비교 (1의 수 차이 1인 쌍):

| 결합 | 결과 | 의미 |
|------|------|------|
| 111 + 101 | 1-1 | $xz$ |
| 111 + 011 | -11 | $yz$ |
| 101 + 001 | -01 | $\overline{y}z$ |
| 011 + 001 | 0-1 | $\overline{x}z$ |
| 001 + 000 | 00- | $\overline{x}\overline{y}$ |

한 번 더:

| 결합 | 결과 | 의미 |
|------|------|------|
| 1-1 + 0-1 (또는 -11 + -01) | --1 | $z$ |

최종 프라임 임플리컨트: $z$(--1)와 $\overline{x}\overline{y}$(00-)

**2단계**: 커버 테이블

| | $xyz$ | $x\overline{y}z$ | $\overline{x}yz$ | $\overline{x}\overline{y}z$ | $\overline{x}\overline{y}\overline{z}$ |
|---|---|---|---|---|---|
| $z$ (--1) | ✓ | ✓ | ✓ | ✓ | |
| $\overline{x}\overline{y}$ (00-) | | | | ✓ | ✓ |

$\overline{x}\overline{y}\overline{z}$는 $\overline{x}\overline{y}$만 커버 → 에센셜. $xyz$는 $z$만 커버 → 에센셜.

**결과: $z + \overline{x}\overline{y}$**

```lean
-- 원래 식
def f_qm (x y z : Bool) : Bool :=
  (x && y && z) || (x && !y && z) || (!x && y && z) ||
  (!x && !y && z) || (!x && !y && !z)

-- 최소화 결과
def f_qm_min (x y z : Bool) : Bool := z || (!x && !y)

-- 동치 검증
example : ∀ x y z : Bool, f_qm x y z = f_qm_min x y z := by decide
```

### 6.4 Lean 4로 퀸-맥클러스키 구현 (간략화)

```lean
-- 비트열 표현 (Some true = 1, Some false = 0, none = '-')
abbrev BitPattern := List (Option Bool)

-- 두 비트열이 한 자리만 다른지 확인
def canCombine (a b : BitPattern) : Option BitPattern :=
  if a.length != b.length then none
  else
    let diffs := a.zip b |>.filter (fun (x, y) => x != y)
    if diffs.length == 1 then
      some (a.zip b |>.map fun (x, y) => if x == y then x else none)
    else none

-- 예시: 111과 101 결합
#eval canCombine [some true, some true, some true]
                  [some true, some false, some true]
-- some [some true, none, some true] = "1-1"
```

---

## 7. 연습문제: 괄호 채우기 (Skeleton)

### 연습 7.1: 간소화 결과 확인

```lean
-- (a) xyz + x̄yz를 간소화하라
-- 힌트: x만 다르므로 x를 제거할 수 있다
-- 결과: yz
example : ∀ x y z : Bool,
  (x && y && z) || (!x && y && z) = ⟨YOUR_EXPRESSION⟩ := by decide

-- (b) wxyz + wx̄yz를 간소화하라
-- 결과: ?
example : ∀ w x y z : Bool,
  (w && x && y && z) || (w && !x && y && z) = ⟨YOUR_EXPRESSION⟩ := by decide
```

<details>
<summary>📝 답 보기</summary>

```lean
-- (a) xyz + x̄yz = yz (x 제거)
example : ∀ x y z : Bool,
  (x && y && z) || (!x && y && z) = y && z := by decide

-- (b) wxyz + wx̄yz = wyz (x 제거)
example : ∀ w x y z : Bool,
  (w && x && y && z) || (w && !x && y && z) = w && y && z := by decide
```

</details>

### 연습 7.2: 카르노맵으로 최소화하기

```lean
-- F(x, y, z) = Σm(0, 2, 4, 5, 6) 를 최소화하라
-- 즉 (0,0,0), (0,1,0), (1,0,0), (1,0,1), (1,1,0)에서 1
-- 카르노맵:
--          yz=00  yz=01  yz=11  yz=10
-- x=0    │  1    │  0    │  0    │  1   │
-- x=1    │  1    │  1    │  0    │  1   │
-- 묶음: (x=1,yz=00)+(x=1,yz=01) = xz̄, 전체 yz=00열 = z̄ȳ... 아니,
-- yz=00 열 전체(2셀) = ȳz̄, yz=10 열 전체(2셀) = yz̄
-- 이 둘을 합치면 4셀 = z̄ (z가 0인 모든 곳)
-- + (x=1,yz=01) 단독 = xȳz
-- 결과: z̄ + xȳz

def f_ex72 (x y z : Bool) : Bool :=
  (!x && !y && !z) || (!x && y && !z) ||
  (x && !y && !z) || (x && !y && z) || (x && y && !z)

def f_ex72_min (x y z : Bool) : Bool := !z || (x && !y && z)
-- 더 간소화: !z || (x && !y) 인가?
-- !z이면 z=false일 때 항상 1. x&&!y&&z는 z=true, x=true, y=false일 때 1.
-- x&&!y는 z에 관계없이... !z || (x && !y)를 확인하자:
-- (0,0,0): !z=1 ✓, (0,0,1): !z=0, x&&!y=0 → 0 ✓ (원래도 0)
-- (1,0,1): !z=0, x&&!y=1 → 1 ✓
-- 맞다!

def f_ex72_min2 (x y z : Bool) : Bool := !z || (x && !y)

example : ∀ x y z : Bool, f_ex72 x y z = f_ex72_min2 x y z := by ⟨YOUR_TACTIC⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y z : Bool, f_ex72 x y z = f_ex72_min2 x y z := by decide
```

</details>

### 연습 7.3: BCD 홀수 판별기 (연습문제 20a)

```lean
-- 10진수 0~9를 BCD로 입력받아, 홀수이면 1을 출력하는 회로를 설계하라
-- 홀수: 1, 3, 5, 7, 9 → z(마지막 비트)가 1인 것들!
-- Don't Care: 10~15

def bcd_odd (w x y z : Bool) : Bool := sorry

-- BCD 유효 범위에서 검증
example : ∀ w x y z : Bool,
  let val := (if w then 8 else 0) + (if x then 4 else 0) +
             (if y then 2 else 0) + (if z then 1 else 0)
  val ≤ 9 →
  bcd_odd w x y z = (val % 2 == 1) := by decide
```

<details>
<summary>📝 답 보기</summary>

```lean
-- 홀수 = 마지막 비트가 1 = z
def bcd_odd (w x y z : Bool) : Bool := z

example : ∀ w x y z : Bool,
  let val := (if w then 8 else 0) + (if x then 4 else 0) +
             (if y then 2 else 0) + (if z then 1 else 0)
  val ≤ 9 →
  bcd_odd w x y z = (val % 2 == 1) := by decide
```

Don't Care 조건 덕분에 최소화 결과가 그냥 $z$ 하나로 끝난다! 입력이 BCD 유효 범위(0~9)에서만 들어온다면, $z$만 보면 홀짝을 판별할 수 있다.

</details>

---

## 8. 도전 연습: `sorry`로 직접 증명

### 연습 8.1: 간소화의 동치성을 `cases`로 증명

```lean
-- xyz + xȳz = xz 를 cases로 증명하라 (decide 사용 금지)
example : ∀ x y z : Bool,
  (x && y && z) || (x && !y && z) = x && z := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y z : Bool,
  (x && y && z) || (x && !y && z) = x && z := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
```

</details>

### 연습 8.2: 복잡한 최소화 검증

```lean
-- Rosen 예제 10의 4변수 최소화:
-- 원래: wxyz + wx̄yz + wxyz̄ + w̄x̄yz + wx̄ȳz + w̄xyz + wxȳz + w̄x̄ȳz̄ + w̄x̄yz̄ + w̄xyz̄ + wxyz̄
-- 이것은 너무 길다. 간단한 버전으로:

-- F = wz + w̄yz̄ 가 올바른 최소화인지 검증
-- (사실 예제 10의 정확한 최소화는 복잡하므로, 간단한 예로 대체)

-- xy + x̄z + yz를 최소화하면 xy + x̄z가 된다 (합의 정리)
-- 증명:
example : ∀ x y z : Bool,
  (x && y) || (!x && z) || (y && z)
    = (x && y) || (!x && z) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y z : Bool,
  (x && y) || (!x && z) || (y && z)
    = (x && y) || (!x && z) := by decide
-- 또는:
-- intro x y z; cases x <;> cases y <;> cases z <;> rfl
```

이것은 **합의 정리**(consensus theorem)라 불리는 유명한 법칙이다: $xy + \overline{x}z + yz = xy + \overline{x}z$. 세 번째 항 $yz$는 나머지 둘에 의해 **이미 커버**되므로 불필요하다.

</details>

---

## 9. 부울 함수 최소화의 복잡도

> ⚠️ 부울 함수 최소화 문제는 **NP-완전**(NP-complete)이다!

이것은 변수가 많아지면 최적 해를 찾는 것이 매우 어렵다는 뜻이다:
- 카르노맵: 4변수까지 실용적, 6변수까지 가능하나 복잡
- 퀸-맥클러스키: 10변수까지 실용적 (지수 복잡도)
- 현대 알고리즘: 25변수까지 가능
- 경험적 방법: 더 큰 입력에 적용 가능하지만 최적을 보장하지 못함

---

## 10. 핵심 요약

| 개념 | 핵심 |
|------|------|
| **최소화** | 같은 기능, 최소 게이트 수 |
| **카르노맵** | 인접 셀 묶기, 2~4변수에 적합 |
| **그레이 코드** | 인접 코드가 1비트만 다름 |
| **프라임 임플리컨트** | 가장 큰 블록 (더 키울 수 없음) |
| **에센셜 프라임 임플리컨트** | 반드시 포함해야 하는 블록 |
| **무정의 조건** | 안 쓰는 입력을 1처럼 활용 |
| **퀸-맥클러스키** | 체계적, 자동화 가능, 지수 복잡도 |
| **합의 정리** | $xy + \overline{x}z + yz = xy + \overline{x}z$ |
| **형식 검증** | `decide`로 최소화 전후 동치 확인 |

---

## 전체 시리즈 회고: Chapter 12 완성!

Part 14-A ~ 14-D를 통해 Rosen 이산수학 **Chapter 12 (부울 대수)** 전체를 다루었다:

| 파트 | 내용 | Rosen 절 |
|------|------|---------|
| **14-A** | 부울 연산, 부울 함수, Bool 타입 | 12.1 전반 |
| **14-B** | 항등식, 쌍대성, 곱의 합 표준형, NAND/NOR | 12.1 후반 + 12.2 |
| **14-C** | 논리 게이트, 회로 설계, 가산기 | 12.3 |
| **14-D** | 카르노맵, 퀸-맥클러스키, 최소화 | 12.4 |
