import Lean
import Lean.Widget

/-!
# UFO diagnostics widget

This module contains the JavaScript/React panel used by the DSL command to show
model diagnostics in Lean-enabled editors. It deliberately contains no parsing,
compilation, or proof-generation logic. The command elaborator only imports the
widget module to get the widget hash needed by `Widget.savePanelWidgetInfo`.
-/

namespace LeanUfo.UFO.DSL

open Lean

@[widget_module]
def ufoDiagnosticsWidget : Widget.Module where
  javascript := "
import * as React from 'react';

const e = React.createElement;

function item(text, key) {
  return e('li', { key }, text);
}

function Section({ title, children }) {
  return e('section', { style: { marginTop: '0.75rem' } },
    e('h4', { style: { margin: '0 0 0.35rem', fontSize: '0.95rem' } }, title),
    children);
}

function MappingTable({ rows }) {
  return e('table', { style: { width: '100%', borderCollapse: 'collapse', fontSize: '0.85rem' } },
    e('thead', null,
      e('tr', null,
        e('th', { style: { textAlign: 'left', borderBottom: '1px solid var(--vscode-panel-border)' } }, 'Name'),
        e('th', { style: { textAlign: 'right', borderBottom: '1px solid var(--vscode-panel-border)' } }, 'Fin index'))),
    e('tbody', null, rows.map((row, i) =>
      e('tr', { key: row.name + i },
        e('td', { style: { padding: '2px 0' } }, row.name),
        e('td', { style: { padding: '2px 0', textAlign: 'right', opacity: 0.75 } }, String(row.index))))));
}

function StatusBadge({ status }) {
  const colors = {
    success: '#2ea043',
    failed: '#f85149',
    pending: '#d29922',
    unchecked: '#8b949e',
    skipped: '#8b949e'
  };
  const color = colors[status] || colors.pending;
  return e('span', {
    style: {
      display: 'inline-block',
      minWidth: '4.4rem',
      color,
      fontWeight: 600,
      textTransform: 'capitalize'
    }
  }, status);
}

function CertificationRow({ row }) {
  return e('div', {
    title: row.formula || row.prop || '',
    style: {
      display: 'grid',
      gridTemplateColumns: '4.8rem max-content max-content 1fr',
      alignItems: 'baseline',
      columnGap: '0.5rem',
      fontSize: '0.85rem',
      marginBottom: '0.2rem',
      minWidth: 'max-content'
    }
  },
    e(StatusBadge, { status: row.status }),
    e('code', null, row.field),
    e('code', {
      style: {
        opacity: 0.75,
        whiteSpace: 'nowrap'
      }
    }, row.prop || ''),
    row.formula
      ? e('span', {
          style: {
            opacity: 0.9,
            whiteSpace: 'nowrap'
          }
        }, row.formula)
      : null);
}

function parseFailureAnalysis(lines) {
  const intro = [];
  const cards = [];
  let current = null;
  let currentEvidence = null;

  const conditionPrefixes = [
    'Need one of:',
    'Required together:',
    'Required but missing:',
    'Forbidden condition:',
    'Missing witness requirements:',
    'Failed condition:'
  ];

  for (const raw of lines || []) {
    const text = String(raw || '');
    if (text.startsWith('Counterexample assignment:')) {
      current = {
        assignment: text.replace('Counterexample assignment:', '').trim(),
        conditionLabel: 'Failed condition',
        condition: '',
        suggestion: '',
        evidence: []
      };
      cards.push(current);
      currentEvidence = null;
    } else if (current && conditionPrefixes.some((prefix) => text.startsWith(prefix))) {
      const prefix = conditionPrefixes.find((candidate) => text.startsWith(candidate));
      current.conditionLabel = prefix.replace(':', '');
      current.condition = text.slice(prefix.length).trim();
      currentEvidence = null;
    } else if (current && text.startsWith('Suggestion:')) {
      current.suggestion = text.replace('Suggestion:', '').trim();
      currentEvidence = null;
    } else if (current && text.startsWith('Evidence for ')) {
      currentEvidence = {
        title: text.replace(/^Evidence for /, '').replace(/:$/, ''),
        items: []
      };
      current.evidence.push(currentEvidence);
    } else if (current && currentEvidence && text.trim().startsWith('- ')) {
      currentEvidence.items.push(text.trim().replace(/^- /, ''));
    } else if (current) {
      current.evidence.push({ title: text, items: [] });
      currentEvidence = null;
    } else {
      intro.push(text);
    }
  }

  return { intro, cards };
}

function FailureAnalysis({ lines }) {
  const parsed = parseFailureAnalysis(lines);
  const cardStyle = {
    border: '1px solid var(--vscode-panel-border)',
    borderRadius: '6px',
    padding: '0.55rem 0.65rem',
    marginTop: '0.5rem',
    background: 'color-mix(in srgb, var(--vscode-editor-foreground) 4%, transparent)'
  };
  const labelStyle = {
    fontSize: '0.72rem',
    opacity: 0.72,
    textTransform: 'uppercase',
    letterSpacing: '0.02em',
    marginBottom: '0.15rem'
  };
  const codeStyle = {
    whiteSpace: 'pre-wrap',
    overflowWrap: 'anywhere'
  };

  return e('div', null,
    parsed.intro.length
      ? e('div', {
          style: {
            borderLeft: '3px solid #d29922',
            padding: '0.35rem 0 0.35rem 0.65rem',
            marginBottom: '0.55rem'
          }
        }, parsed.intro.map((line, i) =>
          e('div', { key: 'intro-' + i, style: { marginBottom: i + 1 === parsed.intro.length ? 0 : '0.2rem' } }, line)))
      : null,
    parsed.cards.map((card, i) =>
      e('div', { key: 'ce-' + i, style: cardStyle },
        e('div', { style: { display: 'flex', alignItems: 'baseline', gap: '0.45rem', marginBottom: '0.45rem' } },
          e('span', { style: { color: '#f85149', fontWeight: 700 } }, 'Counterexample ' + (i + 1)),
          e('code', { style: { opacity: 0.9 } }, card.assignment)),
        card.condition
          ? e('div', { style: { marginBottom: '0.45rem' } },
              e('div', { style: labelStyle }, card.conditionLabel || 'Failed condition'),
              e('code', { style: codeStyle }, card.condition))
          : null,
        card.suggestion
          ? e('div', {
              style: {
                borderLeft: '3px solid #3fb950',
                paddingLeft: '0.55rem',
                marginBottom: '0.45rem'
              }
            },
              e('div', { style: labelStyle }, 'Suggestion'),
              e('div', null, card.suggestion))
          : null,
        card.evidence.length
          ? e('div', null,
              e('div', { style: labelStyle }, 'Evidence'),
              card.evidence.map((group, j) =>
                e('div', { key: 'ev-' + i + '-' + j, style: { marginTop: j === 0 ? 0 : '0.35rem' } },
                  e('code', { style: codeStyle }, group.title),
                  group.items.length
                    ? e('ul', { style: { margin: '0.2rem 0 0', paddingLeft: '1.1rem' } },
                        group.items.map((item, k) =>
                          e('li', { key: 'ev-item-' + k },
                            e('code', { style: codeStyle }, item))))
                    : null)))
          : null)));
}

export default function(props) {
  const facts = props.facts || [];
  const expandedFacts = props.expandedFacts || [];
  const statuses = props.certification || [];
  const failed = statuses.find(s => s.status === 'failed');

  return e('div', {
    style: {
      padding: '0.75rem',
      lineHeight: 1.35,
      maxWidth: 'none',
      overflowX: 'auto'
    }
  },
    e('h3', { style: { margin: '0 0 0.25rem' } }, 'UFO diagnostics'),
    e('div', { style: { opacity: 0.8, marginBottom: '0.5rem' } },
      props.model ? 'Model: ' + props.model : 'DSL model'),
    failed
      ? e('div', { style: { color: '#f85149', fontWeight: 600, marginBottom: '0.5rem' } },
          'Certification stopped at ', failed.field, '.')
      : props.failure
      ? e('div', { style: { color: '#f85149', fontWeight: 600, marginBottom: '0.5rem' } },
          props.failure)
      : e('div', { style: { color: '#2ea043', fontWeight: 600, marginBottom: '0.5rem' } },
          props.stage === 'certified' ? 'All generated certificate checks completed.' : 'Parsed model diagnostics are available.'),

    e(Section, { title: 'Worlds' }, e(MappingTable, { rows: props.worlds || [] })),
    e(Section, { title: 'Things' }, e(MappingTable, { rows: props.things || [] })),

    e(Section, { title: 'Input facts' },
      facts.length
        ? e('ul', { style: { margin: 0, paddingLeft: '1.2rem' } }, facts.map(item))
        : e('div', { style: { opacity: 0.75 } }, 'No input facts recorded.')),

    e(Section, { title: 'Expanded finite facts' },
      expandedFacts.length
        ? e('details', null,
            e('summary', null, expandedFacts.length + ' compiled facts'),
            e('ul', { style: { margin: '0.35rem 0 0', paddingLeft: '1.2rem' } }, expandedFacts.map(item)))
        : e('div', { style: { opacity: 0.75 } }, 'No expanded facts recorded.')),

    (props.failureAnalysis || []).length
      ? e(Section, { title: 'Failure analysis' },
          e(FailureAnalysis, { lines: props.failureAnalysis }))
      : null,

    e(Section, { title: 'Certification' },
      statuses.length
        ? e('details', { open: !!failed },
            e('summary', null,
              failed ? 'Stopped at ' + failed.field : statuses.filter(s => s.status === 'success').length + ' certificate checks'),
            e('div', { style: { marginTop: '0.35rem', overflowX: 'auto' } }, statuses.map((s, i) =>
              e(CertificationRow, { key: s.field + i, row: s }))))
        : e('div', { style: { opacity: 0.75 } }, 'Certification has not started.')))
}
"

end LeanUfo.UFO.DSL
