# Website deployment and recovery

**Public URL:** https://dovvnloading.github.io/loops-research-archive/

**Publishing model:** Root-level static files from branch **main**, folder **/(root)**. No server, build process, custom domain, Jekyll or third-party JavaScript framework is needed for the new homepage.

## Root cause of the outage

On 2026-11-05, the public repository API reported **has_pages: false** even though it was public and already contained index.html, figures, released PDFs, a ledger and web assets. Its previous GitHub Actions workflows performed Lean/Python research checks but **did not deploy to GitHub Pages**. A green research CI run is not a website deployment.

The older homepage also relied on an external React UMD runtime; a failed CDN download could render a blank page. That older page has been preserved at [classic.html](../classic.html). The new index.html is fully static and works without JavaScript. Only ledger filtering is optional progressive enhancement provided by a small local script.

## One-time GitHub administrator action

**The connected GitHub tools in this session cannot edit the GitHub Pages repository setting.** To publish the site, a repository administrator must:

1. Open [Settings → Pages](https://github.com/dovvnloading/loops-research-archive/settings/pages).
2. Under **Build and deployment**, choose **Deploy from a branch**.
3. Select branch **main** and folder **/(root)**.
4. Click **Save**.
5. Check the deployment run in the Actions tab, then visit https://dovvnloading.github.io/loops-research-archive/ .

No CNAME file, new domain, gh-pages branch or separate deploy token is required. The repository already contains .nojekyll and project-relative asset URLs. Subsequent updates to main will use the configured publishing source.

**Do not attempt to enable Pages with the default GITHUB_TOKEN and an enablement flag on actions/configure-pages.** That action requires an independently privileged token for enablement, as stated in its [action metadata](https://github.com/actions/configure-pages/blob/main/action.yml). This repository does not need such a token when its administrator can select branch publishing once.

## Files provided

| Path | Purpose |
| --- | --- |
| index.html | Static accessible homepage and research overview |
| site-v2.css | Responsive design; no external assets |
| site-v2.js | Optional client-side filtering of the ledger |
| ledger.json | 465-entry machine-readable source-locked proof ledger |
| figs/ and figs/readme/ | Figures and two SVG diagrams |
| papers/ | Released paper PDFs, source and QA artifacts |
| marked_width_mlc_manuscript.pdf | Main 225-page manuscript |
| dossier.html | Original visualization dossier |
| classic.html | Preserved original interactive homepage |
| 404.html | Friendly recovery page |
| .nojekyll | Bypass automatic Jekyll processing |
| favicon.svg, robots.txt, sitemap.xml | Site metadata |

## Validation

Run in the repository root:

    python code/verify_site_integrity.py
    node --check site-v2.js
    python -m http.server 8000

Browse http://localhost:8000/ and use the proof-ledger filters. The Site health GitHub Actions workflow checks the complete static site and runs a local HTTP smoke test on relevant PRs and pushes.

The [separate research validation workflow](../.github/workflows/lean-proofs.yml) still checks mathematical code and Lean but does not publish the website.

## Troubleshooting

- **404 and has_pages: false:** GitHub Pages must be enabled in repository Settings → Pages. Research CI success cannot replace this.
- **Pages enabled but still 404:** Verify that source is main / (root), not the docs folder; inspect the GitHub Pages deployment run.
- **Images or PDFs missing:** Confirm the full root publishing source was deployed. All local links are relative to the project subpath.
- **Ledger filtering not working:** The main HTML still loads. Check that ledger.json and site-v2.js were published; open or download the complete ledger directly.
- **Classic homepage blank:** It uses external React/CDN dependencies. The new main homepage is a static-first replacement with no dependency on that runtime.
- **Rollback:** The original page is preserved as classic.html and in Git history. No research papers, ledger statuses or proof certificates were deleted.

## Mathematical status

This is a website publishing and presentation repair, not a mathematical theorem update. The source-locked ledger remains 34 imported, 316 internally proved, 115 open (2026-07-27), and the Mandelbrot Local Connectivity conjecture remains open.

Further references: [GitHub Pages publishing configuration](https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site) and [404 troubleshooting](https://docs.github.com/en/pages/getting-started-with-github-pages/troubleshooting-404-errors-for-github-pages-sites).
