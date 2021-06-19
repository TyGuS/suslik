<template>
    <div class="app--ide">
        <benchmark-list-pane ref="benchmarks"/>
        <editor-pane ref="editors"/>
        <proof-trace-pane ref="proofTrace"/>
    </div>
</template>

<style>
.app--ide {
    display: flex;
}
</style>

<script>
import BenchmarkListPane from './benchmark-list-pane.vue';
import EditorPane from './editor-pane.vue';
import ProofTracePane from './proof-trace-pane.vue';

import Split from 'split.js';


export default {
    mounted() {
        this.makeResizable(this.$el);
    },
    methods: {
        makeResizable($el) {
            this.split = Split($el.querySelectorAll('.ide-pane'), {
                sizes: [10, 45, 45],
                snapOffset: 0,
                minSize: 1000,
                gutterSize: 5
            });
        }
    },
    components: { ProofTracePane, BenchmarkListPane, EditorPane }
}
</script>