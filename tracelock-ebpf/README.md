## Reproducible artifact commands

TraceLock now has three reproducible artifact paths:

1. verified/local core artifact
2. strace real-ingestion artifact
3. eBPF live kernel-ingestion artifact

---

## 1. Full local artifact runner

Run:

```bash
cd ~/k-sentry
./scripts/run_all_local.sh