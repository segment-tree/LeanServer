# Frontend → left / right → backend

独立于 `examples/frontend-backend` 的分支转发例子。应用、证明和测试均在本目录，依赖仓库根目录的 LeanServer 库。

```text
                    ┌→ left  :8082 ─┐
client → frontend   │               ├→ backend :8081
           :8080 ───┤               │
                    └→ right :8083 ─┘
```

frontend 保留原来的认证规则：解析后的 `X-Username` 必须恰好只有一个值 `Tom`，`X-Password` 必须恰好只有一个值 `123456`。头名称大小写不敏感，重复凭据不被接受。`/login` 保留原来的提示响应；最终定理只讨论 GET `/resource`。

认证成功后，根据 **HTTP 解析后的 `request.body.size`** 选择上游：奇数走 left，偶数走 right，空正文走 right。正文可以是任意二进制字节；chunked 请求按解码后的正文计算长度。frontend 移除凭据头。

left、right 使用同一个 `relayWith`，把完整的收到的 `Request` 原样传入 proxy，rewrite 为 `id`，目的地址为 backend。proxy 仍负责移除旧的协议字段并重建 Host、Content-Length、Connection 等；解析还会规范化头值。这不表示两跳 HTTP 字节完全一致。

## 构建和运行

以下命令从仓库根目录运行，工具链为 Lean 4.29.1：

```bash
lake -d examples/frontend-backend2 build frontend left right backend Proof.Proof network-tests
examples/frontend-backend2/.lake/build/bin/network-tests
lake -d examples/frontend-backend2 env lean examples/frontend-backend2/Test/Audit.lean
bash examples/frontend-backend2/Test/smoke.sh
```

`smoke.sh` 要求本机 8080–8083 端口空闲，启动并清理自己的进程。它验证正常请求和凭据拒绝，并停掉 left，检查奇数请求失败而偶数请求仍成功。该故障测试不属于可靠传输契约下的定理。

手动运行时，在四个终端分别启动：

```bash
examples/frontend-backend2/.lake/build/bin/backend
examples/frontend-backend2/.lake/build/bin/left
examples/frontend-backend2/.lake/build/bin/right
examples/frontend-backend2/.lake/build/bin/frontend
```

```bash
# 奇数正文走 left；把 a 换为 ab 则走 right。
curl -X GET --data-binary 'a' \
  -H 'X-Username: Tom' -H 'X-Password: 123456' \
  http://127.0.0.1:8080/resource
```

frontend 默认监听 `0.0.0.0:8080`，其余服务监听 loopback。证明中的可达边是固定网络输入；启动这些进程本身不会安装防火墙来实现图中的所有网络隔离限制。

## 最终证明

入口：[Proof/Proof.lean](Proof/Proof.lean)，命名空间 `FrontendBackend2.Proof`。

```lean
theorem remote_resource_iff_credentials
    (source : Upstream)
    (contracts : Contracts (frontendBackendGraph source))
    (wire : ByteArray) (hRequest : ResourceInput wire) :
    observed (frontendBackendGraph source) contracts wire = expectedResource wire ↔
      credentialsMatch (context wire) = true
```

- `source` 是任意客户端源地址和**源端口**。
- `frontendBackendGraph source` 保存四个实际 handler 和五条固定可达边。client 是特殊发起点，不是 handler。图不由请求、凭据或调用结果生成。
- `wire` 是原始 HTTP 请求字节。`context` 从这些字节解析得到，不能另行指定请求。
- `observed` 执行图中实际 handler 的上游调用，每跳都编码请求、解析收到的字节、计算响应并再编码、解析。观察值是 HTTP 状态码和正文。
- `expectedResource` 是针对原始请求 target 的 backend resource 的状态码和正文，包含 query。

环境预设只有 `Contracts.socket` 和 `Contracts.transport`：前者保证送入 socket 的完整字节原样进入网络；后者保证沿图中可达边传输的完整字节原样收到。响应沿已建立连接返回；`Direction` 区分该连接上的两个传输方向，不增加反向发起调用的图边。

`ResourceInput` 沿用原例子的请求范围：

| 条件 | 范围 |
| --- | --- |
| 解析 | `parseHTTP1` 成功得到完整请求，无剩余字节 |
| 方法和路径 | GET，路径为 `/resource`，允许 query |
| 头数量 | `< 64`，包括重复头 |
| 头名称和值的 UTF-8 字节总量 | `≤ 48 KiB`，不含分隔符和行结束符 |
| target UTF-8 大小 | `≤ 8 KiB` |
| 解码后正文大小 | `≤ 10 MiB` |

这些是定理的原始请求条件，不是新增的 handler 检查，也不要求中间请求满足同样的总头数量条件。

两跳解析成功是证明结论：第一跳头部上界为 57,680 字节；第二跳移除第一跳自动生成的协议头，对每个保留头保守地多计一个分隔空格，上界为 57,743 字节，两者都小于解析器的 65,536 字节限制。method、target、body 的保持以及响应经过 relay/frontend 后状态码和正文的保持均从实现推导，没有 CodecContracts 或 RuntimeCorrespondence。

此外，`ServiceProofs.frontend_odd_call`、`frontend_even_call` 证明认证成功后恰好产生对应分支的一次调用；`relay_identity_call` 证明 relay 恰好向 backend 调用一次，并传入整个原始收到的请求。

## 验证范围

最终证明无 `sorry`、无新增业务公理。依赖检查列出 Lean 的标准逻辑依赖，以及 codec 中 `native_decide` 生成的 `_native.native_decide.ax_*` 计算依赖；这些计算依赖也属于信任边界。

定理验证图执行模型中的实际应用核心和 HTTP codec。它没有证明真实 IO accept/recv/send 循环、C、OS 到图模型的对应关系。`decodeResponse` 是纯观察器，不是 proxy 中带 1 MiB 限制的增量 IO 响应读取器；真实程序的冒烟测试不能代替这种对应证明。

证明文件关系见 [Proof/README.md](Proof/README.md)。测试都在 `Test/`：完整图计算测试、依赖审计、真实服务冒烟测试。
