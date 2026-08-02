# AGENTS.md

Guidance for AI agents working in this repository.

## Permission escalation rule

If a command fails due to insufficient permissions, you must elevate the
command to the user for approval:

- rerun the command with `sandbox_permissions: "require_escalated"`;
- include a short question in the `justification` parameter asking the user
  whether to allow the action;
- optionally suggest a scoped `prefix_rule` for repeated approvals (for
  example `["git", "push"]`).

Do not silently work around permission failures; always route them through
user approval.

## Why this matters here

The sandbox mounts `/home/ubuntu/lean-tla/.git` read-only, so local git
writes (`git add`, `git commit`, `git remote`, `git push`) fail inside the
sandbox with "Read-only file system", even though the workspace files are
writable. Run git commands in the repository directory and elevate on
permission failures as above. If `.git` is still read-only when elevated
(the OS mount is `ro`), use the established fallback: commit from a writable
overlay repo in `/tmp`, then push from there:

```
git clone --depth 1 https://github.com/yihuang/lean-tla.git /tmp/lean-tla-git
git -C /tmp/lean-tla-git --work-tree=/home/ubuntu/lean-tla add -A
git -C /tmp/lean-tla-git -c user.name=yihuang -c user.email=yi.codeplayer@gmail.com commit -m "..."
git -C /tmp/lean-tla-git push origin main
```

The GitHub remote is https://github.com/yihuang/lean-tla.git; gh's git
credential helper authenticates pushes. Network is also restricted in the
sandbox, so pushes need escalation too.
