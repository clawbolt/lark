#!/bin/sh
# 把 lterm 打包成 macOS 的程序（build/lterm.app）：双击、放进 Dock、用 open 启动都行，不用先开一个终端。
# 用法（在 apps/lterm 里）：
#   sh macos/make_app.sh             编译，生成 build/lterm.app
#   sh macos/make_app.sh --install   再装到 ~/Applications（启动台、Spotlight 里能找到）
# 包里只有三样：Contents/MacOS/lterm（就是 build/lterm）、Contents/Info.plist（macos/Info.plist）、PkgInfo；
# macos/lterm.icns 存在时放进去当图标，没有时用系统默认的图标。
# 从包里启动、没有参数时 lterm 直接开窗口（main.lark），在家目录跑登录 shell。
# 签名用 ad-hoc（codesign --sign -）：只在这台机器上用，不用开发者账号。
set -e
cd "$(dirname "$0")/.."

../../build/lark build

APP=build/lterm.app
rm -rf "$APP"
mkdir -p "$APP/Contents/MacOS" "$APP/Contents/Resources"
cp build/lterm "$APP/Contents/MacOS/lterm"
cp macos/Info.plist "$APP/Contents/Info.plist"
printf 'APPL????' > "$APP/Contents/PkgInfo"
if [ -f macos/lterm.icns ]; then
  cp macos/lterm.icns "$APP/Contents/Resources/lterm.icns"
fi
codesign --force --sign - "$APP" >/dev/null 2>&1 || echo "（签名失败：自己编译的程序一般也能打开；打不开时在 Finder 里右键 → 打开）"
echo "生成了 $APP：open $APP"

if [ "$1" = "--install" ]; then
  mkdir -p "$HOME/Applications"
  rm -rf "$HOME/Applications/lterm.app"
  cp -R "$APP" "$HOME/Applications/lterm.app"
  # 让启动台、Spotlight 马上认出来
  /System/Library/Frameworks/CoreServices.framework/Frameworks/LaunchServices.framework/Support/lsregister -f "$HOME/Applications/lterm.app" >/dev/null 2>&1 || true
  echo "装到了 ~/Applications/lterm.app"
fi
