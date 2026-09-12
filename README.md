# 实分析笔记

## 参考用书

- Terence Tao, _Analysis I_, 4th edition, Springer, 2022.
- Terence Tao, _Analysis II_, 4th edition, Springer, 2022.

## 文档结构

```bash
./
├── chapter
│   ├── chapter01.typ
│   ├── chapter02.typ
│   ├── chapter03.typ
│   ├── chapter04.typ  # 各个章节的笔记
│   └── ...
├── main.pdf # 编译产生的 .pdf 文件
├── main.typ # 主文件，所有章节文件会包含其中，并进行全局配置（如字体，数学公式排版等）
├── README.md
└── utils # 放置工具函数
    └── utils.typ # 工具函数定义
```

## 编译文档

0. 下载 `typst` 编译器

   请参阅[官方仓库](https://github.com/typst/typst)的说明

1. 下载字体（可选）

   请前往[官方仓库 release](https://github.com/lxgw/LxgwWenKai)下载

2. 编译

   在终端中运行以下命令

```bash
typst compile ./main.typ
```

3. 阅读

   编译产生的文档默认名为 `main.pdf`

<!--## 勘误记录-->
