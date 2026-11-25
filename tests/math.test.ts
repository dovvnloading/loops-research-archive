import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';
import { angleOrbit, criticalOrbit, doubleAngle, formatRational, parseRational, periodicBinary, rationalToNumber } from '../src/lib/math.ts';

test('rational normalization preserves huge exact certificate integers', () => {
  const numerator = '-607918036626757496169199575185708826140';
  assert.equal(parseRational(`${numerator}/1`).numerator.toString(), numerator);
  assert.equal(formatRational(parseRational('-18/-24')), '3/4');
  assert.throws(() => parseRational('1/0'), RangeError);
  assert.throws(() => parseRational('3.14'), TypeError);
});

test('the certificate’s two distinct accesses collide after six doublings', () => {
  const first = '116791/523264';
  const second = '378423/523264';
  assert.notEqual(first, second);
  assert.equal(doubleAngle(first, 6), '2327/8176');
  assert.equal(doubleAngle(second, 6), '2327/8176');
});

test('period-nine angles return exactly and the symbolic period is preserved', () => {
  assert.equal(doubleAngle('228/511', 9), '228/511');
  assert.equal(new Set(angleOrbit('228/511', 9)).size, 9);
  assert.deepEqual(periodicBinary('228/511'), { prefix: '', period: '011100100', truncated: false });
  assert.deepEqual(periodicBinary('3/7'), { prefix: '', period: '011', truncated: false });
  assert.deepEqual(periodicBinary('1/8'), { prefix: '001', period: '', truncated: false });
  assert.deepEqual(periodicBinary('1/31', 2), { prefix: '00', period: '', truncated: true });
  assert.equal(doubleAngle('-1/3'), '1/3');
});

test('conversion to canvas coordinates is explicitly approximate but finite', () => {
  assert.equal(rationalToNumber('3/4'), 0.75);
  assert.ok(Math.abs(rationalToNumber(`${'1' + '0'.repeat(400)}/${'2' + '0'.repeat(400)}`) - 0.5) < 1e-15);
});

test('critical orbit handles known fixed, periodic, and escaping cases', () => {
  assert.deepEqual(criticalOrbit([0, 0], 4).map(p => [p.re, p.im]), [[0,0],[0,0],[0,0],[0,0],[0,0]]);
  assert.deepEqual(criticalOrbit([-1, 0], 4).map(p => p.re), [0,-1,0,-1,0]);
  const escaping = criticalOrbit([1, 0], 128);
  assert.equal(escaping.at(-1)?.index, 3);
  assert.equal(escaping.at(-1)?.escaped, true);
  assert.throws(() => criticalOrbit([NaN, 0]), RangeError);
});

test('generated browser certificates retain the exact dyadic bracket and source statuses', () => {
  const root = new URL('../public/data/', import.meta.url);
  const tip = JSON.parse(readFileSync(new URL('tip.json', root), 'utf8'));
  const { lower_numerator: lower, upper_numerator: upper, denominator_power_of_two: exponent } = tip.parameter_bracket;
  assert.equal(typeof lower, 'string');
  assert.equal(lower, '-607918036626757496169199575185708826140');
  assert.equal(BigInt(upper) - BigInt(lower), 1n);
  assert.equal(exponent, 128);
  const source = JSON.parse(readFileSync(new URL('../ledger.json', import.meta.url), 'utf8'));
  const browser = JSON.parse(readFileSync(new URL('ledger.json', root), 'utf8'));
  for (const key of ['obligations', 'research_updates']) {
    assert.equal(browser[key].length, source[key].length);
    source[key].forEach((row: {id: string;status: string;statement: string;deps: string[]}, index: number) => {
      for (const field of ['id','status','statement','deps'] as const) assert.deepEqual(browser[key][index][field], row[field]);
    });
  }
  assert.equal(browser.provenance.mlc_status, 'MLC remains open');
});
