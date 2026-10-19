# 证明文件关系

唯一最终入口为 `Proof.lean`，没有 Proofv2 或旧版 Exchange 模型。

```text
FrontendCore / BackendCore / Proxy（实际服务代码）
 ├─ ServiceProofs（认证、奇偶调用、relay 原样传入请求、头过滤）
 │   └─ ForwardingProofs（原始请求限制、三个目的地址、第一次编码长度）
 │       └─ RequestHeadProofs + CodecProofs（实际请求编码/解析）
 │           └─ TwoHopProofs（协议头移除、第二跳长度、两次解析成功）
 ├─ NetworkGraph（Handler AppM、固定可达 DAG）
 └─ ResponseCodecProofs（resource/拒绝响应往返、重复编码）
     └─ NetworkExecution（两类契约、沿图执行、客户端观察）
         └─ ApplicationGraph（frontend / left / right / backend 固定图）

以上结果 → Proof（两跳调用执行、响应返回、最终 iff 定理）
```

`NetworkExecution` 同时依赖 `NetworkGraph`；`Proof` 使用 `TwoHopProofs` 的解析结论和 `ResponseCodecProofs` 的响应结论。图节点只有 handler，图边只有可达性，所有中间请求和响应都由执行计算出来。

底层模块按职责分组：

| 模块 | 作用 |
| --- | --- |
| `ByteFramingProofs`、`RequestFramingProofs` | 字节分段、CRLF 边界定位 |
| `AsciiHTTPProofs`、`HTTPStringProofs`、`StringJoinProofs` | HTTP 字符串拼接和分割 |
| `TrimProofs` | 实际 trim 实现的字符与 UTF-8 长度性质 |
| `DecimalProofs`、`HTTPDecimalProofs` | Content-Length 十进制往返 |
| `ResponseHeadProofs` | JSON 响应头的编码、边界和解析 |

`TwoHopProofs` 的辅助定理有语法、大小等局部条件；它们都从原始 `ResourceInput` 推导并在 `Proof.lean` 中消去，不是最终定理的新预设。`invoke_of_serve` 同样只用于组合已经证明的执行和解码结果，最终定理不接收调用结果或运行对应关系。

运行 `lake -d examples/frontend-backend2 build Proof.Proof` 检查整个依赖链；运行 `Test/Audit.lean` 查看最终定理和路由定理的依赖。
