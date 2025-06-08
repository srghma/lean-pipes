# Haskell Bidirectional Type Transformation Matrix

## Type Definitions

- `a'` - values flowing upstream (input)
- `a` - values flowing downstream (input)
- `b'` - values flowing upstream (output)
- `b` - values flowing downstream (output)

## 4x4 Transformation Table

| From → To           | a' (up input)             | a (down input)             | b' (up output)         | b (down output)         |
| ------------------- | ------------------------- | -------------------------- | ---------------------- | ----------------------- |
| **a' (up input)**   | `id :: a' -> a'`          | `reverse :: a' -> a`       | `process :: a' -> b'`  | `pipeline :: a' -> b`   |
| **a (down input)**  | `upstream :: a -> a'`     | `id :: a -> a`             | `contramap :: a -> b'` | `forward :: a -> b`     |
| **b' (up output)**  | `feedback :: b' -> a'`    | `backpropagate :: b' -> a` | `id :: b' -> b'`       | `downstream :: b' -> b` |
| **b (down output)** | `error_signal :: b -> a'` | `gradient :: b -> a`       | `reflect :: b -> b'`   | `id :: b -> b`          |

## Common Transformation Patterns

### Direct Transformations

- **a' → a**: Flow reversal, often seen in bidirectional parsing or neural networks
- **a → b**: Standard forward processing pipeline
- **b' → b**: Converting upstream output to downstream output

### Feedback Transformations

- **b → a'**: Error propagation or gradient backpropagation
- **b' → a**: Upstream feedback affecting downstream input
- **a' → b**: Direct upstream input to downstream output (bypass)

### Identity Transformations

- **a' → a'**, **a → a**, **b' → b'**, **b → b**: Type-preserving operations

## Typical Use Cases

**Bidirectional Parsers**:

- `a' = ParseResult`, `a = String`, `b' = AST`, `b = Output`

**Neural Networks**:

- `a' = Gradients`, `a = Input`, `b' = BackpropSignal`, `b = Prediction`

**Stream Processing**:

- `a' = Acknowledgment`, `a = Data`, `b' = Status`, `b = ProcessedData`

**Lens-like Structures**:

- `a' = UpdateSignal`, `a = Source`, `b' = ChangeNotification`, `b = View`
