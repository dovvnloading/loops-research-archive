"""Reproduce the period-27 figure from the certified integer records."""
import json
from pathlib import Path
import argparse
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Rectangle

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    out = parser.parse_args().output
    rows = json.loads(Path(__file__).with_name('period27_readout.json').read_text())
    fig = plt.figure(figsize=(8, 4.7), facecolor='white')
    axes = fig.subplots(2, 1, gridspec_kw={'height_ratios':[1,1.15], 'hspace':.60})
    dark, real, twin = '#22374C', '#006B64', '#9F4433'
    ax = axes[0]
    for i, row in enumerate(rows[:2]):
        color = (real,twin)[i]
        for j, bit in enumerate(row['bit_word']):
            ax.add_patch(Rectangle((j,1-i), .89,.73, facecolor=color if bit=='1' else 'white',
                                   edgecolor=color,linewidth=.75))
        ax.text(-.5,1.36-i, ('Airplane','Tuned rabbit')[i],ha='right',va='center',color=dark,fontsize=10)
    for p in (0,9,18,27):
        ax.text(p-.1,-.16,str(p),ha='center',va='top',fontsize=8,color=dark)
    ax.set_xlim(-4.4,27.2); ax.set_ylim(-.5,2.15); ax.axis('off')
    ax.set_title('The two angular words differ in the middle nine bits',loc='left',fontsize=12.5,color=dark)
    ax=axes[1]
    t=np.linspace(0,1,1300)
    a=np.array([1 if v=='0' else -1 for v in rows[0]['bit_word']])
    intensity=np.abs(np.exp(2j*np.pi*t[:,None]*np.arange(len(a)))@a)**2
    ax.plot(t,intensity,color=real,lw=1.45)
    ax.set(xlim=(0,1),ylim=(0,130),xticks=[0,.25,.5,.75,1],yticks=[0,60,120])
    ax.set_xlabel('Frequency in cycles per lattice spacing',fontsize=9)
    ax.spines[['top','right']].set_visible(False)
    ax.spines[['left','bottom']].set_color('#8A989F')
    ax.tick_params(colors=dark,labelsize=8,length=3); ax.grid(axis='y',color='#E4E9E8',linewidth=.6)
    ax.set_title('One intensity curve for both words, and for six more',loc='left',fontsize=12.5,color=dark,pad=8)
    fig.subplots_adjust(left=.1,right=.98,top=.93,bottom=.12)
    fig.savefig(out,bbox_inches='tight',dpi=180)
if __name__=='__main__':
    main()
