-- Lark 的语言服务器 llsp（Neovim 0.11 以上）。
-- 复制到 ~/.config/nvim/plugin/lark.lua，再把 lark_root 改成你的 Lark 仓库路径。
local lark_root = vim.fs.normalize("~/src/lark")

vim.filetype.add({ extension = { lark = "lark" } })

-- 注释和缩进（Lark 用 // 注释，4 个空格缩进）
vim.api.nvim_create_autocmd("FileType", {
  pattern = "lark",
  callback = function()
    vim.bo.commentstring = "// %s"
    vim.bo.expandtab = true
    vim.bo.shiftwidth = 4
    vim.bo.tabstop = 4
  end,
})

vim.lsp.config("llsp", {
  cmd = { lark_root .. "/apps/llsp/build/llsp" },
  cmd_env = { LARK_HOME = lark_root },
  filetypes = { "lark" },
  root_markers = { "lark.pkg", ".git" },
})
vim.lsp.enable("llsp")

-- gd 跳到定义（gO 列出大纲、]d / [d 在诊断之间跳是 Neovim 0.11 默认就有的）
vim.api.nvim_create_autocmd("LspAttach", {
  callback = function(ev)
    local client = vim.lsp.get_client_by_id(ev.data.client_id)
    if client and client.name == "llsp" then
      vim.keymap.set("n", "gd", vim.lsp.buf.definition, { buffer = ev.buf, desc = "跳到定义（llsp）" })
    end
  end,
})
