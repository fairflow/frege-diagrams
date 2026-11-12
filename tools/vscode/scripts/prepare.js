// Copies into the extension what it ships with: the page of the browser
// editor (used when the workspace's frege-diagrams package has none) and the
// licence.  Run by `npm run package`.
const fs = require('fs');
const path = require('path');
const here = path.join(__dirname, '..');
const repo = path.join(here, '..', '..');
fs.mkdirSync(path.join(here, 'media'), { recursive: true });
fs.copyFileSync(path.join(repo, 'tools', 'framedit', 'index.html'), path.join(here, 'media', 'index.html'));
fs.copyFileSync(path.join(repo, 'LICENSE'), path.join(here, 'LICENSE'));
console.log('prepared media/index.html and LICENSE');
