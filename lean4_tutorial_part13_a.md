# Part 13-A: 그래프와 그래프 모델 (Graphs and Graph Models)

> **Rosen 이산수학 8판 · Chapter 10 · Section 10.1 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 12 시리즈에서 **관계**(relation)와 **부분순서**(partial order)를 배웠다. 이제 이산수학에서 가장 흥미롭고 실용적인 주제 중 하나인 **그래프**(graph)를 시작한다!

**그래프**는 **꼭짓점**(vertex, 정점, node)들과 이 꼭짓점들을 연결하는 **모서리**(edge, 변)들로 구성된 이산구조이다. 이것만으로도 놀라울 정도로 다양한 실세계 문제를 모델링할 수 있다:

- 🌐 **소셜 네트워크**: 사람 = 꼭짓점, 친구 관계 = 모서리
- 🖥️ **컴퓨터 네트워크**: 컴퓨터 = 꼭짓점, 통신 링크 = 모서리
- 🗺️ **도로망**: 교차로 = 꼭짓점, 도로 = 모서리
- 📞 **전화 호출**: 전화번호 = 꼭짓점, 통화 = 모서리
- 🧬 **단백질 상호작용**: 단백질 = 꼭짓점, 상호작용 = 모서리

이 파트에서는 다음을 다룬다:

1. **그래프**(graph)의 정의 — 가장 기본적인 수학적 개념
2. **단순 그래프**(simple graph), **다중그래프**(multigraph), **의사그래프**(pseudograph)의 차이
3. **방향성 그래프**(directed graph, digraph)와 **혼합 그래프**(mixed graph)
4. 다양한 **그래프 모델**: 소셜 네트워크, 통신 네트워크, 전화 호출, 웹 그래프 등
5. **Lean 4**에서 그래프를 정의하고 기본 성질을 증명하는 방법

### 이 파트에서 핵심으로 등장하는 Lean 4 개념

| 개념 | 설명 |
|------|------|
| `SimpleGraph V` | Mathlib의 단순 그래프 타입 |
| `structure` | 사용자 정의 그래프 구조체 |
| `Sym2 V` | 비순서 쌍 (무방향 모서리) |
| `Finset` | 유한 집합 (꼭짓점, 모서리 집합) |
| `Prop` | 명제 타입 (인접 관계) |

---

## 1. 그래프란 무엇인가? — 가장 기본적인 정의

### 1.1 일상적 직관

그래프를 이해하는 가장 쉬운 방법은 **점과 선**으로 생각하는 것이다.

```
    서울 ●────────● 부산
         \       |
          \      |
           ●─────●
         대전    대구
```

위 그림에서:
- **점**(●)이 **꼭짓점**(vertex)이다: 서울, 부산, 대전, 대구
- **선**(─)이 **모서리**(edge)이다: 서울-부산, 서울-대전, 부산-대구, 대전-대구

이것이 그래프의 전부이다! 점들과 그것들을 연결하는 선들의 모임.

### 1.2 수학적 정의 (Rosen 정의 1)

> **정의 1** (그래프)
>
> **그래프**(graph) $G = (V, E)$는 공집합이 아닌 **꼭짓점**(vertex, node)들의 집합 $V$와 **모서리**(edge)들의 집합 $E$로 구성된다. 각 모서리는 **끝점**(endpoint)이라 부르는 하나 또는 두 개의 꼭짓점을 가진다. 모서리는 이 끝점들을 연결한다고 한다.

쉽게 풀어 쓰면:

| 구성 요소 | 의미 | 비유 |
|---------|------|------|
| $V$ (꼭짓점 집합) | "점들의 모임" | 도시들, 사람들, 컴퓨터들 |
| $E$ (모서리 집합) | "선들의 모임" | 도로, 친구 관계, 통신 링크 |
| 끝점(endpoint) | 모서리가 연결하는 꼭짓점 | 도로의 양쪽 끝 도시 |

**핵심 포인트**: 꼭짓점의 집합 $V$는 **공집합이 아니어야** 한다! 즉, 점이 하나도 없는 그래프는 존재하지 않는다. (모서리는 없을 수 있다 — 점만 있고 선이 없는 경우도 그래프이다.)

> **참고**: 꼭짓점의 집합 $V$는 무한집합일 수도 있다. 무한개의 꼭짓점을 가진 그래프를 **무한 그래프**(infinite graph)라 하고, 유한개의 꼭짓점 집합 $V$를 가진 그래프를 **유한 그래프**(finite graph)라 한다. 이 교재에서는 보통 유한 그래프들만 다룬다.

---

## 2. 그래프의 종류 — 세상에는 다양한 그래프가 있다!

그래프를 분류할 때 다음 **3가지 핵심 질문**에 답하면 된다:

> 1️⃣ 그래프의 모서리들이 **비방향성**인가 **방향성**인가 (혹은 둘 다인가)?
> 2️⃣ 만약 비방향성이라면 꼭짓점의 쌍을 연결하는 **다중 모서리**가 존재하는가? 방향성이라면 **다중 방향 모서리**가 존재하는가?
> 3️⃣ 주어진 그래프에 **루프**(loop)가 있는가?

이 세 가지 질문의 답에 따라 그래프의 종류가 결정된다. 하나씩 자세히 살펴보자.

### 2.1 비방향성 그래프 — "양방향 도로"

#### 2.1.1 단순 그래프(simple graph) — 가장 깨끗한 그래프

**단순 그래프**(simple graph)는 가장 단순하고 깨끗한 형태의 그래프이다.

**단순 그래프의 규칙**:
- ✅ 각 모서리는 **순서 없는** 꼭짓점들의 쌍이다 (비방향성)
- ❌ **중복 모서리**(같은 쌍을 연결하는 두 개 이상의 모서리)를 **허용하지 않는다**
- ❌ **루프**(자기 자신을 연결하는 모서리)를 **허용하지 않는다**

따라서 단순 그래프에서 꼭짓점의 쌍 {u, v} 사이에는 **최대 하나의 모서리만** 존재한다.

```
단순 그래프의 예:

  a ●──────● b        ✅ 허용: 각 쌍에 최대 1개 모서리
    |      |          ❌ 루프 없음
    |      |          ❌ 다중 모서리 없음
  c ●──────● d
```

**비유**: 단순 그래프는 "깨끗한 도로망"과 같다. 두 도시 사이에는 최대 한 개의 도로만 있고, 출발점과 도착점이 같은 순환 도로는 없다.

#### 중요한 성질

단순 그래프에서 모서리 {u, v}는:
- **순서가 없다**: {u, v} = {v, u} (서울→부산 도로 = 부산→서울 도로, 같은 도로!)
- u ≠ v이다 (루프가 없으므로)

#### Lean 4에서의 단순 그래프

Lean 4의 Mathlib에는 `SimpleGraph`라는 타입이 이미 정의되어 있다. 이것은 정확히 위의 단순 그래프에 대응한다:

```lean
-- Mathlib의 SimpleGraph 정의 (핵심 구조)
-- V는 꼭짓점의 타입
structure SimpleGraph (V : Type*) where
  Adj : V → V → Prop       -- Adj u v : "u와 v가 인접하다"
  symm : ∀ {u v}, Adj u v → Adj v u     -- 대칭성 (비방향성!)
  loopless : ∀ v, ¬ Adj v v             -- 루프 없음!
```

이것을 풀어서 설명하면:

| 필드 | 의미 | 단순 그래프의 성질 |
|------|------|----------------|
| `Adj : V → V → Prop` | "u와 v가 인접하다"는 명제 | 모서리의 존재를 나타냄 |
| `symm` | Adj u v → Adj v u | {u, v} = {v, u} — 비방향성! |
| `loopless` | ¬ Adj v v | 루프 없음! |

**직관**: `SimpleGraph V`는 타입 `V`의 원소들(꼭짓점)에 대해 "누가 누구와 인접하는지"를 말해주는 구조이다. 대칭적(비방향)이고 루프가 없는 것이 핵심이다.

```lean
-- 직접 만들어 보자: 4개의 꼭짓점을 가진 단순 그래프
-- 꼭짓점: 0, 1, 2, 3
-- 모서리: {0,1}, {1,2}, {2,3}, {0,3} (정사각형 모양)

def squareGraph : SimpleGraph (Fin 4) where
  Adj u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1) ∨
    (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 2) ∨
    (u.val = 0 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 0)
  symm := by
    intro u v h
    -- h의 각 경우(Or)를 대칭적으로 뒤집으면 된다
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                  ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    all_goals (first | left | right; constructor <;> assumption)
  loopless := by
    intro v ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    all_goals omega
```

위 코드가 복잡해 보이지만, 핵심 아이디어는 간단하다:
1. `Adj`를 모든 인접 쌍의 목록으로 정의
2. `symm`에서 (u,v) → (v,u)의 대칭성을 증명
3. `loopless`에서 (v,v)가 불가능함을 증명

> 💡 **팁**: 실제로는 Mathlib의 `SimpleGraph.fromRel`이나 인접 행렬을 사용하면 훨씬 간단하게 그래프를 만들 수 있다. 여기서는 구조를 이해하기 위해 직접 만들었다.

#### 더 쉬운 방법: 관계로부터 단순 그래프 만들기

```lean
-- 대칭적이고 비반사적인 관계로부터 단순 그래프를 만드는 함수
-- SimpleGraph.fromRel은 관계 R에서 단순 그래프를 만든다
-- (내부적으로 대칭화를 해준다)

-- 예: 인접 리스트로 그래프 정의
def myAdj : Fin 4 → Fin 4 → Prop
  | 0, 1 => True
  | 1, 2 => True
  | 2, 3 => True
  | 0, 3 => True
  | _, _ => False

-- 이를 대칭화하여 단순 그래프로 만든다
def myGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun u v => myAdj u v)
```

#### 2.1.2 다중그래프(multigraph) — "같은 도시 사이에 여러 도로"

현실에서는 같은 두 도시 사이에 **여러 개의 도로**가 있을 수 있다. 예를 들어, 서울과 부산 사이에는 경부고속도로, KTX 노선, 항공 노선 등이 있다. 이런 상황을 모델링하려면 **다중그래프**(multigraph)가 필요하다.

**다중그래프의 규칙**:
- ✅ 각 모서리는 순서 없는 꼭짓점들의 쌍이다 (비방향성)
- ✅ **다중 모서리**(같은 쌍을 연결하는 여러 모서리)를 **허용한다**
- ❌ **루프**를 **허용하지 않는다**

```
다중그래프의 예:

  a ●══════● b        ✅ 다중 모서리 허용 (이중선 = 2개 모서리)
    |      |          ❌ 루프 없음
  c ●──────● d
```

위 그림에서 a와 b 사이에 **2개의 모서리**가 있다. 순서를 갖지 않는 같은 꼭짓점들의 쌍 {u, v}에 m개의 다른 모서리들이 존재한다면 {u, v}는 m의 **다중모서리**를 가진다. 즉 모서리 {u, v}는 m개 모서리들 집합이다.

**비유**: 다중그래프는 "같은 두 도시를 여러 교통수단으로 연결할 수 있는 교통망"이다.

```lean
-- 다중그래프는 Mathlib의 SimpleGraph로는 표현할 수 없다.
-- (SimpleGraph는 각 쌍에 최대 1개의 모서리만 허용)
-- 직접 구조체를 정의해야 한다:

structure Multigraph (V : Type*) where
  Edge : Type*                        -- 모서리들의 타입
  endpoints : Edge → Sym2 V           -- 각 모서리의 양 끝점 (순서 없는 쌍)
  -- 루프 없음: 끝점이 같지 않아야 함
  no_loop : ∀ e : Edge, ∀ v : V, endpoints e ≠ Quotient.mk _ (v, v)
```

> **Sym2 V**란? `Sym2 V`는 V의 원소들의 **순서 없는 쌍**(unordered pair)을 나타내는 타입이다. {u, v} = {v, u}가 자동으로 성립한다. 이것은 비방향 모서리를 나타내기에 완벽하다!

#### 2.1.3 의사그래프(pseudograph) — "루프도 허용!"

통신망에서는 데이터 센터가 **자기 자신에게** 데이터를 보내는 경우도 있다 (진단 목적 등). 이런 **루프**(loop)도 허용하는 그래프를 **의사그래프**(pseudograph)라 한다.

**의사그래프의 규칙**:
- ✅ 비방향성
- ✅ 다중 모서리 허용
- ✅ **루프 허용** (자기 자신을 연결하는 모서리)

```
의사그래프의 예:

  a ●══════● b        ✅ 다중 모서리 허용
  ↻ |      |          ✅ 루프 허용 (a에 루프!)
  c ●──────● d
```

루프(loop)란? 한 꼭짓점에서 출발하여 **같은 꼭짓점으로 돌아오는** 모서리이다. 위 그림에서 a의 루프(↻)가 그 예이다.

```lean
-- 의사그래프: 루프도 허용
structure Pseudograph (V : Type*) where
  Edge : Type*
  endpoints : Edge → Sym2 V  -- 루프도 자연스럽게 (v, v)로 표현됨
  -- 루프를 금지하는 조건이 없다!
```

### 2.2 방향성 그래프 — "일방통행 도로"

지금까지 소개한 그래프는 **비방향성 그래프**(undirected graph)이다. 모서리에 방향이 없다. 하지만 그래프 모델을 구성하기 위해 그래프의 모서리에 **방향이 필요할 때**도 있다.

예를 들어 컴퓨터 네트워크에서 어떤 통신망들은 **단지 한 방향으로만** 동작할 수 있다. 이런 통신망/링크를 단방향 이중방식 선(single duplex lines)이라 한다. 한 방향으로만 많은 양의 트래픽을 보내는 경우에 해당한다.

이런 상황에서는 **방향성 그래프**(directed graph)를 사용한다.

#### 정의 2 (방향성 그래프)

> **방향성 그래프**(다이그래프: directed graph 또는 digraph) $(V, E)$는 공집합이 아닌 꼭짓점들의 집합 $V$와 **방향모서리**(방향아크: directed edges 또는 directed arcs)들의 집합 $E$로 구성된다. 각 방향모서리는 꼭짓점들의 **순서쌍**이다. 순서쌍 $(u, v)$에 관련된 방향모서리는 $u$에서 **시작**(start)하여 $v$에서 **끝난다**(end)고 부른다.

핵심 차이: **비방향 모서리**는 {u, v} (순서 없음), **방향 모서리**는 (u, v) (순서 있음!)

```
비방향성 그래프:             방향성 그래프:
  a ●──────● b              a ●──────→ b
  (a-b = b-a)               (a→b ≠ b→a!)
```

**비유**: 
- 비방향성 모서리 = 양방향 도로 (서울 ↔ 부산)
- 방향성 모서리 = 일방통행 도로 (서울 → 부산만 가능)

#### 방향성 그래프를 그릴 때

방향성 그래프를 그릴 때는 u에서 v로의 **화살표**를 사용하여 (즉, u → v), u에서 시작하여 v에서 끝나는 모서리의 방향을 나타낸다.

#### 방향성 그래프의 특수한 경우들

**단순방향성 그래프**(simple directed graph):
- 방향 모서리는 순서쌍
- **루프 없음**: (v, v) 형태의 모서리 없음
- **다중 방향 모서리 없음**: 각 순서쌍 (u, v)에 최대 하나의 모서리
- **양방향 가능**: (u, v)와 (v, u)는 서로 다른 모서리 — 둘 다 존재할 수 있다!

> 주의: 비방향성 그래프의 각 모서리에 **방향을 부여하면** 방향성 그래프를 얻을 수 있다. 방향성 그래프에 루프와 다중 방향 모서리가 하나도 없을 때는 **단순방향성 그래프**(simple directed graph)라 한다.

```lean
-- Lean 4에서 방향성 그래프 (단순)
structure SimpleDigraph (V : Type*) where
  Adj : V → V → Prop                    -- 방향 인접: (u, v)
  loopless : ∀ v, ¬ Adj v v             -- 루프 없음
  -- 주의: symm가 없다! 방향성이므로 Adj u v ↛ Adj v u
```

비교:

| | SimpleGraph | SimpleDigraph |
|---|---|---|
| `symm` | ✅ 있음 | ❌ 없음 |
| `loopless` | ✅ 있음 | ✅ 있음 |
| Adj u v → Adj v u | 항상 성립 | 반드시 성립하지 않음 |

**방향성 다중 그래프**(directed multigraph):
- 한 꼭짓점에서 같은 꼭짓점(또는 다른 꼭짓점)으로의 **다중 방향성 모서리**(multiple directed edges)를 허용
- 루프도 허용
- 두 개의 서로 다른 두 꼭짓점 u, v에 대응하는 하나의 순서쌍 (u, v)에 서로 다른 m개의 방향성 모서리들이 존재하면 (u, v)를 **중복도**(multiplicity)가 m인 **다중 모서리**(multiple edges)라 부른다

```lean
-- 방향성 다중 그래프
structure DirectedMultigraph (V : Type*) where
  Edge : Type*
  src : Edge → V    -- 각 모서리의 시작점
  tgt : Edge → V    -- 각 모서리의 끝점
  -- 다중 모서리, 루프 모두 허용!
```

### 2.3 혼합 그래프(mixed graph) — "비방향 + 방향 모두!"

어떤 모델에서는 비방향성 모서리와 방향성 모서리를 **동시에** 사용해야 한다. 이런 그래프를 **혼합 그래프**(mixed graph)라 한다.

**비유**: 도로망에서 **양방향 도로**와 **일방통행 도로**가 모두 존재하는 경우가 혼합 그래프이다.

```lean
-- 혼합 그래프
structure MixedGraph (V : Type*) where
  UndirEdge : Type*                    -- 비방향 모서리
  DirEdge : Type*                      -- 방향 모서리
  undirEndpoints : UndirEdge → Sym2 V  -- 비방향 모서리의 끝점들
  dirSrc : DirEdge → V                 -- 방향 모서리의 시작점
  dirTgt : DirEdge → V                 -- 방향 모서리의 끝점
```

### 2.4 그래프 용어 종합 정리표 (Rosen 표 1)

아래 표는 여러 가지 종류의 그래프들에 대한 용어를 요약한다:

| 종류 | 모서리들 | 다중 모서리 | 루프 |
|------|---------|----------|------|
| **단순 그래프**(simple graph) | 비방향성 | ❌ 허용하지 않음 | ❌ 허용하지 않음 |
| **멀티그래프**(multigraph) | 비방향성 | ✅ 허용 | ❌ 허용하지 않음 |
| **의사그래프**(pseudograph) | 비방향성 | ✅ 허용 | ✅ 허용 |
| **단순 방향성 그래프**(simple directed graph) | 방향성 | ❌ 허용하지 않음 | ❌ 허용하지 않음 |
| **방향성 다중 그래프**(directed multigraph) | 방향성 | ✅ 허용 | ✅ 허용 |
| **혼합 그래프**(mixed graph) | 방향성과 비방향성 | ✅ 허용 | ✅ 허용 |

> **중요**: 문맥이 분명할 때 그래프라는 일반적인 용어로서 **그래프**라는 용어를 사용한다. "그래프"라는 용어는 **비방향성 그래프만**을 나타낼 때 사용한다.

### 2.5 그래프의 구조를 이해하는 3가지 핵심 질문

그래프를 설명하는 용어들이 서로 다르더라도 다음 3개의 중요한 질문은 그래프의 구조를 이해하는 데 도움을 줄 것이다:

1. 그래프의 모서리들이 **비방향성**인가 **방향성**인가 (혹은 둘 다인가)?
2. 만약 비방향성이라면 꼭짓점들의 쌍을 연결하는 **다중 모서리**가 존재하는가? 방향성이라면 **다중 방향 모서리**가 존재하는가?
3. 주어진 그래프에 **루프**가 있는가?

그래프를 표현하는 데 사용된 특정 용어(그래프, 방향성그래프, 단순방향성 그래프, 방향성 다중 그래프 등)들을 기억하는 것 보다, **위 질문에 답을 주는 것**이 그래프를 이해하는 데 더 도움이 될 것이다.

---

## 3. 그래프 모델들 — 실세계 응용

주위의 다양한 모델에서 그래프를 이용한다. 이 절에서는 통신 네트워크를 연결하는 데이터 센터들을 연결하는 그래프 모델로 건설하는지 살펴보는 것에서 시작하여, 몇 가지 흥미있는 응용에 대응하는 그래프 모델들을 소개하는 것으로 마무리하려 한다.

### 3.1 소셜네트워크(social networks)

**소셜네트워크**(social networks)에서 그래프는 사람들 혹은 사람들의 모임 사이의 다양한 관계를 표현하는 사회적 구조를 모델링하는 데 광범위하게 이용된다. 이런 사회적 구조와 이를 표현하는 그래프를 **소셜네트워크**라 한다.

#### 예제 1: 교우관계 그래프(acquaintanceship and friendship graphs)

단순 그래프는 사람 간의 다양한 관계를 표현하는 데도 사용된다. 예를 들어, 두 사람이 서로 아는 사이인지 또는 (실세계에서 혹은 Facebook 같은 소셜네트워크 같은 가상세계에서) 친한 친구들인지를 구분하여 표현할 수 있다.

사람들이 모인 특정 그룹에서 각 사람을 **꼭짓점**(vertex)으로 표현할 수 있다. 이 사람들이 서로 알거나 친구일 때 **비방향성 모서리**(undirected edge)를 사용하여 두 사람을 연결한다. 다중 모서리와 루프는 보통 사용하지 않는다.

- **어떤 종류의 그래프?** → **단순 그래프** (비방향, 다중 모서리 없음, 루프 없음)
- 세상 모든 사람의 교우관계 그래프는 60억 개 이상의 꼭짓점과 대략 1조 개 이상의 모서리를 가질 것이다!

```lean
-- 교우관계 그래프 모델
-- 사람들의 집합과 "서로 아는 관계"로 단순 그래프를 만든다
-- (대칭적: 내가 너를 알면 너도 나를 안다)

-- 작은 예: 5명의 교우관계
inductive Person5 : Type
  | Alice | Bob | Charlie | Diana | Eve
  deriving DecidableEq, Fintype, Repr

open Person5

def friendshipAdj : Person5 → Person5 → Prop
  | Alice, Bob => True      -- Alice와 Bob은 친구
  | Bob, Alice => True
  | Bob, Charlie => True    -- Bob과 Charlie는 친구
  | Charlie, Bob => True
  | Alice, Diana => True    -- Alice와 Diana는 친구
  | Diana, Alice => True
  | Diana, Eve => True      -- Diana와 Eve는 친구
  | Eve, Diana => True
  | _, _ => False

-- 단순 그래프 구성
-- (대칭성과 비반사성을 만족함)
```

#### 예제 2: 영향력 그래프(influence graph)

'특정 사람들이 다른 사람들의 생각과 판단에 영향을 미칠 수 있다'는 연구결과는 집단행동(group behavior) 연구를 통하여 증명되는데, **영향력 그래프**라고 하는 **방향성 그래프**가 이런 상황을 모델링하는 데 사용될 수 있다.

일단 집단의 각 사람들을 꼭짓점으로 표현하고, 꼭짓점 a로 표현된 사람이 꼭짓점 b로 표현된 사람의 생각과 판단에 영향을 미칠 때, 꼭짓점 a에서 b로의 **방향 모서리**가 존재하는 것으로 표현한다.

```
   Deborah → Brian
   Deborah → Fred
   Deborah → Linda
   (아무도 Deborah에게 영향을 주지 않는다!)
   Yvonne ↔ Brian (서로 영향)
```

- **어떤 종류의 그래프?** → **방향성 그래프** (영향은 일방적일 수 있으므로!)

```lean
-- 영향력 그래프: 방향성 그래프의 예
-- 꼭짓점 a에서 b로의 방향 모서리 = "a가 b에 영향을 줄 수 있다"

def influenceAdj : Person5 → Person5 → Prop
  | Alice, Bob => True      -- Alice가 Bob에게 영향
  | Alice, Charlie => True   -- Alice가 Charlie에게 영향
  | Bob, Alice => True       -- Bob도 Alice에게 영향 (양방향)
  | _, _ => False

-- 이것은 SimpleGraph가 아니다! (대칭적이지 않을 수 있으므로)
-- SimpleDigraph가 적합하다
```

#### 예제 3: 공동작업(협력) 그래프(collaboration graph)

공동작업 그래프는 특정한 방식에 따라 작업을 같이 수행하는 두 사람 사이의 관계를 소셜네트워크로 모델링하는 데 사용된다. 공동작업 그래프는 비방향성 모서리를 갖고 루프와 다중 모서리가 없기 때문에 **단순 그래프**의 예이다.

**할리우드 그래프**(Hollywood graph): 꼭짓점들은 배우들을 나타내고, 이 꼭짓점들에 의해 나타낸 배우들이 영화나 텔레비전 쇼에 함께 출연한 경우, 두 꼭짓점을 연결한다. 할리우드 그래프는 2018년 초 현재 290만 개 이상의 꼭짓점을 갖는 거대한 그래프이다.

**학술 공동연구 그래프**(academic collaboration graph): 꼭짓점은 연구자들을 나타내고, 모서리는 논문의 공동 저자들을 연결한다.

### 3.2 통신 네트워크들

다양한 통신 네트워크를 모델링할 때 장치(device)들은 꼭짓점으로 나타내고 통신 링크들은 모서리로 표현한다.

#### 컴퓨터 네트워크 (Rosen 그림 1, 2)

데이터 센터들과 통신링크로 연결된 컴퓨터들의 네트워크:
- 각 데이터 센터의 위치는 점으로, 각 통신망은 선분으로 표현
- **단순 그래프** 또는 **다중그래프** (같은 두 센터 사이에 여러 링크가 있을 수 있으므로)

```
컴퓨터 네트워크 (단순 그래프):
                Detroit
San Francisco ●────● Chicago ●────● New York
              \   |         |    /
               ● Denver    ● Washington
              /
   Los Angeles
```

### 3.3 전화 호출 그래프(call graphs)

통신사의 장거리 전화 네트워크와 같이 네트워크에서 전화 호출(call)을 모델링할 때도 그래프를 사용할 수 있다. 특히, **방향 다중 그래프**(directed multigraph)로 전화 호출 상황을 모델링할 수 있다.

- 각 전화번호는 **꼭짓점**으로 표현
- 각 전화 호출은 **방향 모서리**로 나타냄 (호출자 → 수신자)
- 같은 번호에서 같은 번호로 여러 번 호출할 수 있으므로 **다중 방향성 모서리**가 필요

```lean
-- 전화 호출 그래프 모델
-- 방향 다중 그래프: 같은 방향으로 여러 번 호출 가능

structure CallRecord where
  caller : String    -- 호출자 전화번호
  callee : String    -- 수신자 전화번호
  time : Nat         -- 호출 시간 (식별용)
  deriving Repr

-- 호출 기록 리스트가 곧 방향 다중 그래프의 모서리 리스트
def callLog : List CallRecord := [
  ⟨"732-555-1234", "732-555-9876", 1⟩,
  ⟨"732-555-1234", "732-555-9876", 2⟩,   -- 같은 쌍에 두 번 호출!
  ⟨"732-555-1234", "732-555-9876", 3⟩,   -- 세 번째 호출!
  ⟨"732-555-9876", "732-555-1234", 4⟩,   -- 역방향 호출 2번
  ⟨"732-555-9876", "732-555-1234", 5⟩,
  ⟨"732-555-0069", "732-555-0011", 6⟩
]
```

### 3.4 웹 그래프(web graph)

월드와이드웹(WWW)은 **방향성 그래프**로 모델링할 수 있다:
- 각각의 인터넷 홈페이지(web page)를 **꼭짓점**으로 표현
- 하나의 홈페이지 a에서 다른 홈페이지 b를 가리키는 **링크**가 존재한다면 a에서 시작해서 b에서 끝나는 **모서리**를 배정
- 거의 매초마다 새 홈페이지가 생성되고, 많은 웹 페이지들은 사라지기 때문에 웹 그래프는 항상 변화

### 3.5 인용 그래프(citation graphs)

그래프는 학술 논문, 특허, 법률의견과 같은 다양한 종류의 문서들에서 인용관계를 나타낼 때도 사용된다:
- 각 문서를 **꼭짓점**으로 표현
- 첫 번째 문서에서 인용목록에 있는 두 번째 문서를 인용하면 첫 번째에서 두 번째 문서로의 모서리를 배정
- **루프와 다중 모서리가 없는 방향그래프**이다

### 3.6 소프트웨어 설계 응용들

#### 예제 7: 모듈 종속성 그래프(module dependency graphs)

소프트웨어를 설계할 때 가장 중요한 작업 중 하나가 '프로그램을 여러개의 부분들이나 모듈로 구조화하는 방법'이다. **모듈 종속성 그래프**는 프로그램 모듈들 간의 상호동작을 이해하는 데 유용한 도구이다.

- 각 모듈들은 꼭짓점으로 나타내고
- 두 번째 모듈이 첫 번째 모듈에 의존(종속)한다면 방향모서리는 첫 번째 모듈에서 두 번째 모듈로 연결

#### 예제 8: 우선순위 그래프와 동시처리(precedence graphs and concurrent processing)

컴퓨터 프로그램은 여러 명령문들을 동시에 실행함으로써 보다 빠르게 실행될 수 있다. 그 과정에서 아직 실행되지 않은 명령문의 결과를 요구하는 문장은 실행 안 하는 것도 중요하다.

- 각 명령문을 꼭짓점으로 표현
- 두 번째 꼭짓점으로 표현한 명령문이 첫 번째 꼭짓점에 의해 표현한 명령문이 수행되기 전에는 실행할 수 없는 경우, 첫 번째 꼭짓점에서 두 번째 꼭짓점으로 모서리를 연결
- 이런 그래프를 **우선순위 그래프**(precedence graph)라 부른다

### 3.7 운송 네트워크(transportation networks)

도로, 항공, 철도, 선박 네트워크와 같은 다양한 운송 네트워크를 모델링하는 데도 그래프가 사용된다.

#### 예제 9: 항공로(airline routes)

항공 네트워크에서 각 공항을 꼭짓점으로 표현하고 출발공항에서 도착공항으로 연결하는 각 비행을 방향모서리로 나타내면, 출발공항과 도착공항이 같은 비행 스케줄이 하루에도 여러 번 있을 수 있기 때문에(다중 비행), 그렇게 만들어진 항공로 그래프는 **방향 다중 그래프**(directed multigraph)이다.

#### 예제 10: 도로지도(road networks)

그래프는 도로지도를 만드는 데도 사용된다:
- 꼭짓점(vertex)은 **교차로**(intersection)를 나타내고
- 모서리(edge)는 **도로**(road)를 나타낸다
- 양방향 도로 → 비방향성 모서리
- 일방통행(one-way) → 방향성 모서리
- 여러 개의 양방향 도로 → 다중 비방향성 모서리
- 회전하는 도로 → 루프
- **혼합 그래프**(일방통행과 양방향 도로를 모두 포함)가 적합!

### 3.8 생물 네트워크(Biological networks)

생명과학의 많은 부분이 그래프를 이용하여 모델링이 가능하다.

#### 예제 11: 생태학에서의 지위 중복 그래프(niche overlap graphs)

동물 중 다른 종(species) 사이의 상호 관계(interaction links)를 포함한 많은 모델들에서 그래프를 사용한다. 예를 들면, 생태계에서 종간의 경쟁은 생태학 **지위 중복 그래프**를 이용하여 표현할 수 있다. 각 종은 꼭짓점으로 표현한다. 만약 두 종이 경쟁한다면(즉, 그들이 필요로 하는 먹이 자원의 일부가 겹치면) 비방향 모서리로 두 꼭짓점을 연결한다.

#### 예제 12: 단백질 상호작용 그래프(protein interaction graphs)

살아 있는 세포에서 단백질의 상호작용은 두 가지 이상의 단백질들이 결합하여 생물학적 기능을 수행할 때 일어난다. 한 세포 내의 단백질 상호작용은 **단백질 상호작용 그래프**(또는 **단백질–단백질 상호작용 네트워크**)를 사용하여 모델링할 수 있다.

### 3.9 시맨틱 네트워크와 토너먼트

#### 시맨틱(의미론) 네트워크

**의미결합관계**(semantic relation)는 단어의 의미에 기초한 두 개 이상의 단어 사이의 관계이다. 꼭짓점이 명사를 나타내고 두 명사가 비슷한 의미를 가질 때 두 꼭짓점이 연결되는 대응하는 그래프를 만들 수 있다.

#### 예제 14: 라운드-로빈 토너먼트(round-robin tournament)

각 팀은 각각 다른 팀과 정확하게 한 번 경기하고 무승부를 허용하지 않는 토너먼트를 **라운드-로빈 토너먼트**(round-robin tournament, 풀리그)라 한다. 이런 토너먼트는 **방향성 그래프**를 사용해서 모델링할 수 있다.

- 각 팀을 꼭짓점으로 표현
- (a, b)는 팀 a가 b를 이겼을 때의 모서리(edge)를 의미

```lean
-- 라운드-로빈 토너먼트 모델
-- 4팀이 참가하는 토너먼트
-- 모든 쌍이 정확히 한 번 경기 (방향: 승자 → 패자)

-- 토너먼트: 모든 서로 다른 쌍에 정확히 하나의 방향이 있는 그래프
structure Tournament (V : Type*) where
  beats : V → V → Prop
  irrefl : ∀ v, ¬ beats v v                    -- 자기 자신을 이기지 않음
  total : ∀ u v, u ≠ v → beats u v ∨ beats v u  -- 모든 쌍에 승패 결정
  antisymm : ∀ u v, beats u v → ¬ beats v u    -- 이기면 지지 않음
```

#### 예제 15: 승자진출권 토너먼트

각 출전자들이 한 게임에서라도 지면 바로 탈락하는 토너먼트를 **승자진출권 토너먼트**(single-elimination tournament, 풀러그)라 한다. 승자진출권 토너먼트는 테니스 게임이나 NCAA 농구 챔피언십 토너먼트와 같은 스포츠에서 사용한다.

---

## 4. Lean 4 기초 연습 — 단순 그래프 다루기

이제 배운 내용을 Lean 4로 직접 실습해 보자. **설명 → 괄호 채우기(skeleton) → sorry 빈칸 채우기** 순서로 진행한다.

### 4.1 Lean 4에서 theorem과 lemma의 관계

Lean 4에서 `theorem`과 `lemma`는 **완전히 동일하다**. 차이가 없다! Lean 4에서 `lemma`는 `theorem`의 **별명**(alias)일 뿐이다.

수학에서는 보통:
- **보조정리**(lemma) = 다른 정리를 증명하기 위한 작은 정리
- **정리**(theorem) = 중요한 결과

하지만 Lean 4에서는 기능적 차이가 전혀 없으므로, 어느 것을 쓰든 상관없다.

```lean
-- 이 두 가지는 완전히 동일하다:
theorem myTheorem : 1 + 1 = 2 := by norm_num
lemma myLemma : 1 + 1 = 2 := by norm_num
```

### 4.2 if(→)와 if and only if(↔)의 차이

Lean 4에서 두 가지 중요한 논리 연결사의 차이를 이해하자:

| 기호 | 이름 | 의미 | Lean 4 |
|------|------|------|--------|
| → | **조건문**(if ... then) | P이면 Q | `P → Q` |
| ↔ | **쌍조건문**(if and only if) | P이면 Q이고, Q이면 P | `P ↔ Q` |

**→ (한 방향)**: "P이면 Q이다" = "P → Q"
- 한 방향만! P에서 Q로 가는 길만 있다.
- P가 참이면 Q도 참이지만, Q가 참이라고 해서 P가 참인지는 모른다.

**↔ (양방향)**: "P이면 Q이고, Q이면 P이다" = "P ↔ Q"
- 양방향! P에서 Q로, Q에서 P로 모두 갈 수 있다.
- P와 Q가 정확히 같은 조건에서 참이다.

```lean
-- → (한 방향) 예시
example : ∀ n : ℕ, n > 5 → n > 3 := by
  intro n h
  omega

-- ↔ (양방향) 예시
example : ∀ n : ℕ, n = 0 ↔ n + 1 = 1 := by
  intro n
  constructor          -- ↔를 두 방향으로 분리!
  · intro h            -- → 방향: n = 0이면 n + 1 = 1
    omega
  · intro h            -- ← 방향: n + 1 = 1이면 n = 0
    omega
```

**↔를 사용하는 핵심 전술들**:

| 전술 | 용도 |
|------|------|
| `constructor` | ↔를 → 와 ← 두 방향으로 분리 |
| `h.mp` 또는 `h.1` | ↔의 → 방향 추출 |
| `h.mpr` 또는 `h.2` | ↔의 ← 방향 추출 |
| `rw [h]` | ↔를 이용한 치환도 가능! |

```lean
-- rw는 ↔도 이용할 수 있다!
-- 이것이 "치환/대입 = 슈퍼포지션"의 핵심이다
example (h : P ↔ Q) (hp : P) : Q := by
  rw [h] at hp    -- hp : P를 hp : Q로 치환!
  exact hp

-- 또는 더 직접적으로:
example (h : P ↔ Q) (hp : P) : Q := by
  exact h.mp hp   -- h.mp : P → Q를 적용
```

### 4.3 치환/대입(rewriting) = 슈퍼포지션(superposition)

Lean 4의 `rw` 전술은 **등식**(=)뿐만 아니라 **동치**(↔)도 이용하여 치환할 수 있다. 이것이 바로 **슈퍼포지션**(superposition)의 아이디어이다:

> "같은 것은 같은 것으로 바꿀 수 있다"

```lean
-- 등식(=)을 이용한 치환
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]    -- 목표가 b + 1 = b + 1이 되고, 자동으로 닫힌다

-- 동치(↔)를 이용한 치환
example (P Q : Prop) (h : P ↔ Q) (goal : P) : Q := by
  rwa [h] at goal
  -- rwa = rw + assumption (치환 후 자동으로 가설 사용)
```

### 연습 4.1: 단순 그래프의 대칭성 이해 (설명 + skeleton)

**문제**: 단순 그래프에서 Adj u v이면 Adj v u임을 이해하고 증명하라.

**설명**: `SimpleGraph`의 `symm` 필드가 이것을 보장한다. `G.symm`을 사용하면 된다.

```lean
-- skeleton: 빈칸을 채워라!
example (G : SimpleGraph V) (u v : V) (h : G.Adj u v) : G.Adj v u := by
  exact G.⟨___⟩ h    -- 어떤 필드를 사용해야 할까?
```

<details>
<summary>📝 답 보기</summary>

```lean
example (G : SimpleGraph V) (u v : V) (h : G.Adj u v) : G.Adj v u := by
  exact G.symm h
```

</details>

### 연습 4.2: 단순 그래프의 비반사성 이해 (설명 + skeleton)

**문제**: 단순 그래프에서 Adj v v가 거짓(¬ Adj v v)임을 증명하라.

**설명**: `SimpleGraph`의 `loopless` 필드가 이것을 보장한다.

```lean
-- skeleton: 빈칸을 채워라!
example (G : SimpleGraph V) (v : V) : ¬ G.Adj v v := by
  exact G.⟨___⟩ v    -- 어떤 필드?
```

<details>
<summary>📝 답 보기</summary>

```lean
example (G : SimpleGraph V) (v : V) : ¬ G.Adj v v := by
  exact G.loopless v
```

</details>

### 연습 4.3: Adj의 대칭성을 ↔로 표현 (skeleton)

**문제**: `G.Adj u v ↔ G.Adj v u`를 증명하라.

**힌트**: `constructor`로 분리한 후 각 방향에 `G.symm`을 사용하라.

```lean
example (G : SimpleGraph V) (u v : V) : G.Adj u v ↔ G.Adj v u := by
  ⟨___⟩           -- ↔를 분리하는 전술
  · intro h       -- → 방향
    exact G.⟨___⟩ h
  · intro h       -- ← 방향
    exact G.⟨___⟩ h
```

<details>
<summary>📝 답 보기</summary>

```lean
example (G : SimpleGraph V) (u v : V) : G.Adj u v ↔ G.Adj v u := by
  constructor
  · intro h
    exact G.symm h
  · intro h
    exact G.symm h
```

</details>

### 연습 4.4: → 와 ↔의 차이 실습 (설명 + skeleton)

**문제**: P → Q에서 Q → P를 유도할 수 없음을 이해하라. 하지만 P ↔ Q에서는 두 방향 모두 추출 가능하다.

```lean
-- → 에서는 한 방향만!
example (h : P → Q) (hp : P) : Q := by
  exact ⟨___⟩ ⟨___⟩    -- h와 hp를 사용

-- ↔ 에서는 양방향!
example (h : P ↔ Q) (hp : P) : Q := by
  exact h.⟨___⟩ hp     -- .mp 또는 .mpr 중 어느 것?

example (h : P ↔ Q) (hq : Q) : P := by
  exact h.⟨___⟩ hq     -- .mp 또는 .mpr 중 어느 것?
```

<details>
<summary>📝 답 보기</summary>

```lean
example (h : P → Q) (hp : P) : Q := by
  exact h hp

example (h : P ↔ Q) (hp : P) : Q := by
  exact h.mp hp     -- .mp = → 방향 (forward)

example (h : P ↔ Q) (hq : Q) : P := by
  exact h.mpr hq    -- .mpr = ← 방향 (backward)
```

</details>

### 연습 4.5: rw로 ↔ 치환하기 (skeleton)

**문제**: `rw`를 사용하여 ↔를 치환하라.

```lean
example (h : P ↔ Q) (hp : P) : Q := by
  ⟨___⟩ [h] at hp    -- hp를 치환하는 전술
  exact hp
```

<details>
<summary>📝 답 보기</summary>

```lean
example (h : P ↔ Q) (hp : P) : Q := by
  rw [h] at hp       -- hp : P를 hp : Q로 치환!
  exact hp
```

</details>

### 연습 4.6: 단순 그래프 직접 정의하기 (sorry)

**문제**: 3개의 꼭짓점 {0, 1, 2}과 모서리 {0,1}, {1,2}를 가진 **경로 그래프**(path graph)를 정의하라.

```lean
-- 경로 그래프: 0 — 1 — 2
def pathGraph3 : SimpleGraph (Fin 3) where
  Adj u v := sorry   -- 인접 관계를 정의하라
  symm := by sorry   -- 대칭성을 증명하라
  loopless := by sorry -- 루프 없음을 증명하라
```

<details>
<summary>📝 답 보기</summary>

```lean
def pathGraph3 : SimpleGraph (Fin 3) where
  Adj u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1)
  symm := by
    intro u v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; left; exact ⟨h2, h1⟩
    · left; exact ⟨h2, h1⟩
    · right; right; right; exact ⟨h2, h1⟩
    · right; right; left; exact ⟨h2, h1⟩
  loopless := by
    intro v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    all_goals omega
```

</details>

### 연습 4.7: theorem과 lemma가 동일함을 확인 (설명)

```lean
-- theorem과 lemma는 Lean 4에서 완전히 같다!
-- 아래 두 선언은 동일한 효과를 가진다:

theorem adj_symm_theorem (G : SimpleGraph V) (u v : V) :
    G.Adj u v → G.Adj v u := G.symm

lemma adj_symm_lemma (G : SimpleGraph V) (u v : V) :
    G.Adj u v → G.Adj v u := G.symm

-- 둘 다 정확히 같은 타입, 같은 증명!
-- #check adj_symm_theorem  -- ... → ...
-- #check adj_symm_lemma    -- ... → ...
```

### 연습 4.8: 방향성 그래프 정의하기 (sorry)

**문제**: 3개의 꼭짓점과 모서리 (0→1), (1→2)를 가진 방향성 그래프를 정의하라.

```lean
structure SimpleDigraph (V : Type*) where
  Adj : V → V → Prop
  loopless : ∀ v, ¬ Adj v v

def directedPath3 : SimpleDigraph (Fin 3) where
  Adj u v := sorry
  loopless := by sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
def directedPath3 : SimpleDigraph (Fin 3) where
  Adj u v :=
    (u.val = 0 ∧ v.val = 1) ∨    -- 0 → 1
    (u.val = 1 ∧ v.val = 2)       -- 1 → 2
    -- 주의: (1,0)이나 (2,1)은 없다! (방향성)
  loopless := by
    intro v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    all_goals omega
```

</details>

### 연습 4.9: 방향성 vs 비방향성 차이 증명 (sorry)

**문제**: 단순 그래프에서 인접 관계가 대칭적임을 증명하라 (Adj u v ↔ Adj v u). 방향성 그래프에서는 이것이 **일반적으로 성립하지 않음**을 이해하라.

```lean
-- 단순 그래프: 대칭!
theorem simpleGraph_adj_comm (G : SimpleGraph V) (u v : V) :
    G.Adj u v ↔ G.Adj v u := by
  sorry

-- 방향성 그래프: 대칭이 아닐 수 있다!
-- directedPath3에서 0 → 1이지만 1 → 0은 아니다
-- 이것은 증명이 아니라 반례를 제시하는 것으로 확인
```

<details>
<summary>📝 답 보기</summary>

```lean
theorem simpleGraph_adj_comm (G : SimpleGraph V) (u v : V) :
    G.Adj u v ↔ G.Adj v u := by
  constructor
  · exact G.symm
  · exact G.symm
```

</details>

### 연습 4.10: 그래프 종류 판별 연습 (이론)

다음 각 상황에서 적합한 그래프의 종류를 판별하라:

**(a)** 두 도시를 주간 고속도로(interstate highway)가 연결한다면 도시를 나타내는 꼭짓점들 사이에 모서리가 존재한다.
- → **단순 그래프** (비방향, 다중 모서리 없음, 루프 없음)

**(b)** 두 도시를 연결하는 고속도로가 있으며, 도시를 나타내는 꼭짓점 사이에 모서리가 존재한다.
- → **다중그래프** (비방향, 같은 두 도시 사이에 여러 고속도로가 있을 수 있음)

**(c)** 도시를 나타내는 꼭짓점들과 그 도시들을 연결하는 고속도로가 있으며, 두 꼭짓점 사이에 모서리가 존재하고, 하나의 도시를 순환하는 고속도로가 있으면 그 도시를 나타내는 꼭짓점에 루프가 존재한다.
- → **의사그래프** (비방향, 다중 모서리, 루프 모두 허용)

**(d)** 비행을 시작하는 도시를 나타내는 꼭짓점에서 비행이 끝나는 도시를 나타내는 꼭짓점으로 향하는 모서리를 그려라.
- → **방향 다중 그래프** (방향성, 같은 노선에 여러 비행)

**(e)** 비행을 시작하는 도시를 나타내는 꼭짓점에서 비행이 끝나는 도시를 나타내는 꼭짓점으로 향하는 모서리를 각 비행에 대해 그려라.
- → **방향 다중 그래프** (방향성, 각 비행마다 모서리)

### 연습 4.11: 토너먼트 정의 (sorry)

**문제**: 3팀 (0, 1, 2)의 라운드-로빈 토너먼트를 정의하라. 결과: 팀0이 팀1을 이기고, 팀1이 팀2를 이기고, 팀2가 팀0을 이긴다 (순환!).

```lean
def tournament3 : Tournament (Fin 3) where
  beats u v := sorry
  irrefl := by sorry
  total := by sorry
  antisymm := by sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
def tournament3 : Tournament (Fin 3) where
  beats u v :=
    (u.val = 0 ∧ v.val = 1) ∨   -- 팀0이 팀1을 이김
    (u.val = 1 ∧ v.val = 2) ∨   -- 팀1이 팀2를 이김
    (u.val = 2 ∧ v.val = 0)     -- 팀2가 팀0을 이김 (순환!)
  irrefl := by
    intro v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    all_goals omega
  total := by
    intro u v hne
    fin_cases u <;> fin_cases v <;> simp_all
    all_goals (first | left | right)
    all_goals constructor <;> rfl
  antisymm := by
    intro u v h1 h2
    rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
    all_goals rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩
    all_goals omega
```

</details>

---

## 5. 핵심 요약

1. **그래프**(graph) $G = (V, E)$는 꼭짓점 집합 $V$와 모서리 집합 $E$로 구성된 이산구조이다.
2. **단순 그래프**(simple graph): 비방향, 다중 모서리 없음, 루프 없음 → Lean 4의 `SimpleGraph`.
3. **다중그래프**(multigraph): 비방향, 다중 모서리 허용, 루프 없음.
4. **의사그래프**(pseudograph): 비방향, 다중 모서리 허용, 루프 허용.
5. **단순 방향성 그래프**(simple directed graph): 방향, 다중 모서리 없음, 루프 없음.
6. **방향성 다중 그래프**(directed multigraph): 방향, 다중 모서리 허용, 루프 허용.
7. **혼합 그래프**(mixed graph): 방향성과 비방향성 모서리 모두 포함.
8. 그래프를 분류하는 **3가지 질문**: 방향성? 다중 모서리? 루프?
9. `SimpleGraph V`는 `Adj : V → V → Prop` + `symm` + `loopless`로 정의된다.
10. `→`(if)는 한방향, `↔`(iff)는 양방향. `theorem`과 `lemma`는 Lean 4에서 동일하다.
11. `rw`는 등식(=)뿐 아니라 동치(↔)도 이용해 치환할 수 있다 — 이것이 **슈퍼포지션**이다.

---

## 6. 사용된 Lean 4 전술 정리

| 전술/키워드 | 용도 | 예시 |
|-----------|------|------|
| `structure` | 새 타입 정의 | `structure SimpleDigraph (V : Type*) where ...` |
| `constructor` | ∧, ↔ 분리 | `constructor` → 두 개의 목표 생성 |
| `rcases` | Or/And 분해 | `rcases h with ⟨a, b⟩ \| ⟨c, d⟩` |
| `fin_cases` | 유한 타입 모든 경우 | `fin_cases u <;> fin_cases v` |
| `omega` | 자연수/정수 산술 | 부등식, 불가능한 경우 처리 |
| `rw` | 치환 (=, ↔ 모두) | `rw [h]`, `rw [h] at hp` |
| `rwa` | rw + assumption | `rwa [h] at hp` |
| `exact` | 정확한 증명 항 제공 | `exact G.symm h` |
| `.mp` | ↔의 → 방향 | `h.mp hp` |
| `.mpr` | ↔의 ← 방향 | `h.mpr hq` |
| `theorem` / `lemma` | 정리 선언 (동일) | 둘 다 같은 기능! |
| `simp_all` | 모든 가설로 단순화 | 자동 증명에 유용 |

---

> **다음 파트 예고**: Part 13-B에서는 **그래프 용어와 특별한 그래프**(Rosen 10.2절)를 다룬다. **차수**(degree), **인접**(adjacency), **근접**(incidence), **이웃**(neighborhood), **악수 정리**(Handshaking Theorem), 그리고 **완전 그래프** $K_n$, **순환 그래프** $C_n$, **바퀴 그래프** $W_n$, **이분 그래프**(bipartite graph) 등의 특별한 그래프를 Lean 4로 구현한다!
