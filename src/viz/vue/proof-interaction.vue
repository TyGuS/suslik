<template>
    <ul class="proof-interaction-choices">
        <li class="choice" v-for="(choice, $i) in choices" :key="$i">
            <div class="goal" v-for="goal in choice" :key="goal.id"
                    @click="selectGoal($event, goal)">
                <span class="title">{{goal.id}}</span>
                <proof-trace-goal :value="goal"/>
            </div>
        </li>
    </ul>
</template>

<script>
import ProofTraceGoal from './proof-trace-goal.vue';


export default {
    props: ['choices'],
    methods: {
        selectGoal(ev, goal) {
            this.$emit('action', {type: 'select', goal});
        }
    },
    components: { ProofTraceGoal }
}
</script>
