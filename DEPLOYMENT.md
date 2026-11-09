# 双版本 GitHub Pages

仅用于 `Shedarshian/deductrium`，保留原 fork 关系。

| 源分支 | 发布位置 | 地址 |
|---|---|---|
| `main` | 根目录 | https://shedarshian.github.io/deductrium/ |
| `feature/model-theory` | `model-theory/` | https://shedarshian.github.io/deductrium/model-theory/ |

两个源分支都保留 `.github/workflows/pages.yml`。推送任一分支或手动运行该 workflow 时，读取两条分支的最新远端提交，只复制页面、CSS、JS、source map 及对应源码和原 README，然后统一发布。无需运行游戏、测试或安装依赖；网页直接使用分支中已提交的 JS，修改 TS 后仍须先编译并提交对应产物。

`gh-pages` 是自动生成的发布分支，不用于开发或手动合并。每次更新同时汇集两个版本，避免只发布其中一个版本而覆盖另一个。`versions.json` 记录本次两个源提交。工作流串行执行，分支更新不使用强制推送。

Pages 设置中的 Source 使用 **GitHub Actions**。工作流一方面更新 `gh-pages` 留存完整静态站点，另一方面通过官方 Pages artifact/deploy action 部署同一份内容，避免 `GITHUB_TOKEN` 推送发布分支不触发 Pages 构建的问题。`github-pages` 环境的发布分支须允许 `main` 和 `feature/model-theory`。

正式版保持原存档键；模型论分支使用带 `-model-theory` 后缀的存档键。不会自动读取或迁移正式版进度。存档编码仍按生存/创造模式区分，与浏览器存储键解耦。语言设置可继续共享。

恢复旧的单版本发布时，在 Pages 设置中切回 `main` 的根目录，并停用本工作流，避免后续自动部署再次切换站点内容。
