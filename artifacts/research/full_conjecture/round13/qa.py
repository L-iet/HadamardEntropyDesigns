# SPDX-License-Identifier: Apache-2.0
"""Generate contact sheets and audit existing research manifests."""
from pathlib import Path
from PIL import Image, ImageDraw
import hashlib,json
root=Path(__file__).resolve().parent
for folder in ('phase_route','spectral_repair','research'):
    pages=sorted((root/'.build'/folder).glob('preview-*.png'))
    assert pages,folder
    for start in range(0,len(pages),6):
        sheet=Image.new('RGB',(1800,1600),'#bbbbbb')
        for index,path in enumerate(pages[start:start+6]):
            page=Image.open(path).convert('RGB');page.thumbnail((580,760))
            x=(index%3)*600+10;y=(index//3)*800+25
            sheet.paste(page,(x,y));ImageDraw.Draw(sheet).text((x,y-20),path.name,fill='black')
        sheet.save(root/'.build'/folder/f'contact-{start//6+1}.png')
for number in range(3,14):
    directory=root.parent/f'round{number}'
    record=json.loads((directory/'verification.json').read_text(encoding='utf-8'))
    for path,digest in record['files'].items():
        assert hashlib.sha256((directory/path).read_bytes()).hexdigest()==digest,(number,path)
    print(directory.name,len(record['files']),'hashes match')
