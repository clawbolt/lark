// Lark 的语言服务器 llsp 的 VS Code 扩展：只负责启动 llsp，功能都在 llsp 里。
const fs = require("fs");
const path = require("path");
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

// PATH 里有没有这个程序
function onPath(name) {
  for (const d of (process.env.PATH || "").split(path.delimiter)) {
    if (d && fs.existsSync(path.join(d, name))) return true;
  }
  return false;
}

function activate(context) {
  const cfg = vscode.workspace.getConfiguration("llsp");
  const env = Object.assign({}, process.env);
  const home = cfg.get("larkHome");
  if (home) env.LARK_HOME = home;

  // 没设置 llsp.path 时，用仓库里构建出来的 apps/llsp/build/llsp（扩展在 apps/llsp/editors/vscode 里）
  let cmd = cfg.get("path");
  let repo = home;
  if (!cmd || cmd === "llsp") {
    // 扩展是用链接（ln -s）装进 ~/.vscode/extensions 的时候，顺着链接找回仓库里的目录
    let dir = context.extensionPath;
    try {
      dir = fs.realpathSync(dir);
    } catch (_) {}
    const local = path.join(dir, "..", "..", "build", "llsp");
    if (fs.existsSync(local)) {
      cmd = local;
      if (!repo) repo = path.join(dir, "..", "..", "..", "..");
    } else {
      cmd = "llsp";
    }
  }
  if (cmd === "llsp" && !onPath("llsp")) {
    vscode.window
      .showErrorMessage(
        "找不到 llsp：请在设置里把 llsp.path 填成 llsp 的完整路径（仓库里的 apps/llsp/build/llsp），llsp.larkHome 填成仓库路径。",
        "打开设置"
      )
      .then((x) => x && vscode.commands.executeCommand("workbench.action.openSettings", "llsp"));
    return;
  }
  // 构建出来的程序有时会丢掉执行权限（比如目录被同步工具重写过）：启动前补上，和 make perms 一样。
  // llsp 本身，以及它发诊断时要运行的 build/lark1
  for (const f of [cmd, repo && path.join(repo, "build", "lark1")]) {
    if (f && path.isAbsolute(f) && fs.existsSync(f)) {
      try {
        fs.chmodSync(f, 0o755);
      } catch (_) {}
    }
  }
  const run = { command: cmd, args: [], options: { env } };
  client = new LanguageClient(
    "llsp",
    "Lark (llsp)",
    { run, debug: run },
    { documentSelector: [{ scheme: "file", language: "lark" }] }
  );
  client.start();
  context.subscriptions.push({ dispose: () => client && client.stop() });

  // 改了设置以后提示重新加载
  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("llsp")) {
        vscode.window
          .showInformationMessage("llsp 的设置改了，重新加载窗口以后生效。", "重新加载")
          .then((x) => x && vscode.commands.executeCommand("workbench.action.reloadWindow"));
      }
    })
  );
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
